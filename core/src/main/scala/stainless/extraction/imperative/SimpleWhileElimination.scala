/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package imperative

trait SimpleWhileElimination
  extends oo.CachingPhase
    with IdentitySorts
    with SimplyCachedFunctions
    with SimpleFunctions
    with oo.IdentityTypeDefs
    with oo.IdentityClasses
    with utils.SyntheticSorts { self =>

  val s: Trees
  val t: s.type

  import s._
  import exprOps._

  protected class TransformerContext(val symbols: Symbols) {
    // we precompute the set of expressions that contain a return
    val exprHasReturn = collection.mutable.Set[Expr]()
    for (fd <- symbols.functions.values) {
      postTraversal {
        case e @ Return(_) => exprHasReturn += e
        case e @ Operator(es, _) if (es.exists(exprHasReturn)) => exprHasReturn += e
        case _ => ()
      }(fd.fullBody)
    }

    val funHasReturn: Set[Identifier] = symbols.functions.values.collect {
      case fd if exprHasReturn(fd.fullBody) => fd.id
    }.toSet

    // and the set of expressions that contain a while
    val exprHasWhile = collection.mutable.Set[Expr]()
    for (fd <- symbols.functions.values) {
      postTraversal {
        case e @ While(_, _, _) => exprHasWhile += e
        case e @ Operator(es, _) if (es.exists(exprHasWhile)) => exprHasWhile += e
        case _ => ()
      }(fd.fullBody)
    }

    val funHasWhile: Set[Identifier] = symbols.functions.values.collect {
      case fd if exprHasWhile(fd.fullBody) => fd.id
    }.toSet
  }

  /* Extract functional result value. Useful to remove side effect from conditions when moving it to post-condition */
  def getFunctionalResult(expr: Expr): Expr = postMap {
    case Block(_, res) => Some(res)
    case _ => None
  }(expr)

  override protected def getContext(symbols: Symbols) = new TransformerContext(symbols)

  protected def extractFunction(tc: TransformerContext, fd: FunDef): FunDef = {
    implicit val symboms = tc.symbols

    // we transform `fd` if the function contains a "simple" `While` loop with no return inside
    val transform = exists {
      case wh @ While(_, _, _) => !tc.exprHasReturn(wh)
      case _ => false
    } (fd.fullBody)

    if (transform) {
      object WhileTransformer extends SelfTreeTransformer {
        override def transform(expr: Expr): Expr = expr match {
          case wh @ While(cond, body, optInv)
            if !tc.exprHasReturn(cond) && !tc.exprHasReturn(body) && optInv.forall(inv => !tc.exprHasReturn(inv)) =>

            val transformedCond = transform(cond)
            val transformedBody = transform(body)
            val transformedInv = optInv.map(transform)

            val id = FreshIdentifier(fd.id.name + "While")
            val tpe = FunctionType(Seq(), UnitType().copiedFrom(wh)).copiedFrom(wh)

            val specced = BodyWithSpecs(transformedBody)
            val measure = specced.getSpec(MeasureKind).map(_.expr)

            val ite =
              IfExpr(
                transformedCond,
                ApplyLetRec(id, Seq(), tpe, Seq(), Seq()).copiedFrom(wh),
                UnitLiteral().copiedFrom(wh)
              ).copiedFrom(wh)

            val newBody =
              Block(
                Seq(transformedBody),
                ite
              ).copiedFrom(wh)

            val newPost =
              Lambda(
                Seq(ValDef.fresh("_unused", UnitType().copiedFrom(wh)).copiedFrom(wh)),
                and(
                  Not(getFunctionalResult(cond).copiedFrom(cond)).copiedFrom(cond),
                  transformedInv.getOrElse(BooleanLiteral(true).copiedFrom(wh))
                ).copiedFrom(wh)
              ).copiedFrom(wh)

            val fullBody = withPostcondition(
              withPrecondition(
                withMeasure(newBody, measure).copiedFrom(wh),
                Some(andJoin(transformedInv.toSeq :+ getFunctionalResult(cond)))
              ).copiedFrom(wh),
              Some(newPost)
            ).copiedFrom(wh)

            LetRec(
              Seq(LocalFunDef(id, Seq(), Seq(), UnitType().copiedFrom(wh), fullBody, Seq()).copiedFrom(wh)),
              IfExpr(
                transformedCond,
                ApplyLetRec(id, Seq(), tpe, Seq(), Seq()).copiedFrom(wh),
                UnitLiteral().copiedFrom(wh)
              ).copiedFrom(wh)
            ).copiedFrom(wh)

          case _ => super.transform(expr)
        }
      }

      fd.copy(fullBody = WhileTransformer.transform(fd.fullBody)).setPos(fd)
    }
    else fd
  }
}

object SimpleWhileElimination {
  def apply(trees: Trees)(implicit ctx: inox.Context): ExtractionPipeline {
    val s: trees.type
    val t: trees.type
  } = new SimpleWhileElimination {
    override val s: trees.type = trees
    override val t: trees.type = trees
    override val context = ctx
  }
}
