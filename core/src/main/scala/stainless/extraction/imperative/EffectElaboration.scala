/* Copyright 2009-2020 EPFL, Lausanne */

package stainless
package extraction
package imperative

trait EffectElaboration
  extends oo.CachingPhase
     with SimpleSorts
     with oo.IdentityTypeDefs
     with oo.SimpleClasses
     with StateInstrumentation { self =>
  val s: Trees
  val t: s.type
  import s._

  // Function rewriting depends on the effects analysis which relies on all dependencies
  // of the function, so we use a dependency cache here.
  override protected final val funCache = new ExtractionCache[s.FunDef, FunctionResult](
    (fd, context) => getDependencyKey(fd.id)(context.symbols)
  )

  // Function types are rewritten by the transformer depending on the result of the
  // effects analysis, so we again use a dependency cache here.
  override protected final val sortCache = new ExtractionCache[s.ADTSort, SortResult](
    (sort, context) => getDependencyKey(sort.id)(context.symbols)
  )

  // Function types are rewritten by the transformer depending on the result of the
  // effects analysis, so we again use a dependency cache here.
  override protected final val classCache = new ExtractionCache[s.ClassDef, ClassResult](
    (cd, context) => getDependencyKey(cd.id)(context.symbols)
  )

  override protected type FunctionResult = Option[t.FunDef]
  override protected def registerFunctions(symbols: t.Symbols,
      functions: Seq[Option[t.FunDef]]): t.Symbols =
    symbols.withFunctions(functions.flatten)

  protected case class EffectTransformerContext(symbols: Symbols)
    extends InstrumentationContext
  { context =>
    def checkEffects(fd: FunDef): Unit = {
      def assertPureIn(expr: Expr, what: String): Unit = {
        import instrumenter._
        instrument(expr)(PurityCheckOn(what))(dummyState)
      }

      exprOps.preTraversal {
        case Require(pre, _)              => assertPureIn(pre, "precondition")
        case Ensuring(_, Lambda(_, post)) => assertPureIn(post, "postcondition")
        case Decreases(meas, _)           => assertPureIn(meas, "measure")
        case Forall(_, pred)              => assertPureIn(pred, "forall quantification")
        case Assert(cond, _, _)           => assertPureIn(cond, "assertion")
        case Assume(cond, _)              => assertPureIn(cond, "assumption")
        case While(_, _, pred, pred2, _)  =>
          pred.foreach(assertPureIn(_, "loop invariant"))
          pred2.foreach(assertPureIn(_, "no-return loop invariant"))
        case MatchExpr(_, cses) =>
          cses.foreach { cse =>
            cse.optGuard.foreach { guard => assertPureIn(guard, "case guard") }
            patternOps.preTraversal {
              case up: UnapplyPattern => assertPureIn(???, "pattern unapply")
              case _ => ()
            }(cse.pattern)
          }
        case Let(vd, e, _) if vd.flags.contains(Lazy) => assertPureIn(e, "lazy val")
        case _ =>
      }(fd.fullBody)
    }
  }

  override protected type TransformerContext = EffectTransformerContext
  override protected def getContext(symbols: Symbols) = EffectTransformerContext(symbols)

  override protected def extractSymbols(tctx: TransformerContext, symbols: s.Symbols): t.Symbols = {
    super.extractSymbols(tctx, symbols)
      .withSorts(Seq(refSort))
  }

  override protected def extractFunction(tctx: EffectTransformerContext,
      fd: FunDef): Option[FunDef] =
  {
    import tctx._
    import symbols._
    import instrumenter._
    import dsl._

    checkEffects(fd)

    // Transform body
    val fdAdjusted = adjustFunSig(fd)
    val initialState = fdAdjusted.params.head.toVariable
    // TODO: Move introduction of MutableMaps into a separate phase
    // val body1 = fdAdjusted.fullBody
    // val body1 = makeHeapMutationExplicit(fdAdjusted.fullBody)
    val body1 = refTransformer.transform(fd.fullBody)
    val body2 = ensureInstrum(instrument(body1)(NoPurityCheck)(initialState))
    val body3 = exprOps.postconditionOf(body2).map { case lam @ Lambda(params, post) =>
      val newPost = exprOps.postMap {
        case Old(e) => Some(instrumentPure(e, initialState))
        case _ => None
      }(post)
      exprOps.withPostcondition(body2, Some(Lambda(params, newPost).copiedFrom(lam)))
    }.getOrElse(body2)
    Some(fdAdjusted.copy(fullBody = body3))
  }

  override protected def extractSort(tctx: EffectTransformerContext, sort: ADTSort): ADTSort =
    sort

  override protected def extractClass(tctx: EffectTransformerContext, cd: ClassDef): ClassDef =
    cd
}

object EffectElaboration {
  def apply(trees: Trees)(implicit ctx: inox.Context): ExtractionPipeline {
    val s: trees.type
    val t: trees.type
  } = new EffectElaboration {
    override val s: trees.type = trees
    override val t: trees.type = trees
    override val context = ctx
  }
}
