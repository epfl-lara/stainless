/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package inlining

/** Inlines, in the lifted function of each method, the lifted functions of its overrides, so that a call
  * unfolds once to the implementations, rather than once per level of the class hierarchy.
  *
  * [[methods.MethodLifting]] lifts each declaration of a method to a function that dispatches on the class
  * of its receiver to the functions of the overrides (which share the symbol of the method), and calls go
  * through the root declaration (see `MethodLifting.rootCall`). Unfolding a call then unfolds one function
  * per level of the hierarchy, and one per override, even when the overrides only read a field or return a
  * constant. In [[xlang.MemberClasses]], the outer accessors of member classes are such methods, and the field
  * types of member classes call them.
  *
  * An override is inlined when it has a body, and no contract or flag that makes its call differ from its
  * body (such as `@extern` or `@opaque`), and when inlining doesn't duplicate calls: its flattened body makes at most one
  * call, which replaces the inlined one, or the dispatch is its only caller. An override that reaches itself
  * through the overrides it inlines is not inlined again. The inlined body keeps its VCs in its own function
  * only.
  */
class DispatchFlattening(override val s: Trees, override val t: Trees)
                        (using override val context: inox.Context)
  extends CachingPhase with NoSummaryPhase with SimpleFunctions with IdentitySorts { self =>

  override protected final val funCache = new ExtractionCache[s.FunDef, (FunctionResult, FunctionSummary)]((fd, context) =>
    getDependencyKey(fd.id)(using context.symbols)
  )

  protected class TransformerContext(val symbols: s.Symbols) {
    import s._
    import symbols.given

    private def symbolOf(id: Identifier): Option[Symbol] = id match {
      case sid: ast.SymbolIdentifier => Some(sid.symbol)
      case _ => None
    }

    /** Whether a call of `fd` is its body, so that it can be inlined. */
    private def inlinable(fd: FunDef): Boolean =
      symbolOf(fd.id).isDefined &&
      exprOps.BodyWithSpecs(fd.fullBody).specs.isEmpty &&
      !exprOps.exists { case _: NoTree => true case _ => false } (fd.fullBody) &&
      !fd.flags.exists {
        case Extern | Opaque | Law | InlineOnce | Inline => true
        case _ => false
      }

    private def calls(e: Expr): Int = exprOps.count { case _: FunctionInvocation => 1 case _ => 0 } (e)

    /** The number of overrides of each method that call each function of the same method. */
    private lazy val parents: Map[Identifier, Int] = symbols.functions.values.toSeq.flatMap { fd =>
      exprOps.collect[Identifier] {
        case FunctionInvocation(gid, _, _) if gid != fd.id && symbolOf(gid) == symbolOf(fd.id) => Set(gid)
        case _ => Set.empty
      } (fd.fullBody).toSeq
    }.groupBy(id => id).view.mapValues(_.size).toMap.withDefaultValue(0)

    private val flattened = scala.collection.mutable.Map[Identifier, Expr]()

    /** The body of `id` with the overrides it dispatches to inlined, where `seen` are the overrides
      * being inlined. */
    private def flatten(id: Identifier, seen: Set[Identifier]): Expr = flattened.getOrElse(id, {
      val fd = symbols.getFunction(id)
      val sym = symbolOf(id)
      val res = exprOps.postMap {
        case fi @ FunctionInvocation(gid, tps, args) if symbolOf(gid) == sym && !seen(gid) &&
            inlinable(symbols.getFunction(gid)) =>
          val body = flatten(gid, seen + gid)
          if (calls(body) > 1 && parents(gid) > 1) None
          else {
            val gfd = symbols.getFunction(gid)
            val inlined = FunctionInvocation(gid, tps, args).inlined(using symbols.withFunctions(Seq(gfd.copy(fullBody = body))))
            Some(Annotated(inlined, Seq(DropVCs)).copiedFrom(fi))
          }
        case _ => None
      } (fd.fullBody)
      if (seen.size == 1) flattened(id) = res
      res
    })

    def transform(fd: FunDef): t.FunDef = {
      val newFd = if (symbolOf(fd.id).isEmpty) fd else fd.copy(fullBody = flatten(fd.id, Set(fd.id)))
      identity.transform(newFd)
    }

    private object identity extends inox.transformers.Transformer with inox.transformers.DefinitionTransformer {
      override val s: self.s.type = self.s
      override val t: self.t.type = self.t
      override type Env = Unit
      override def initEnv: Env = ()
    }
  }

  override protected def getContext(symbols: s.Symbols) = new TransformerContext(symbols)

  override protected def extractFunction(context: TransformerContext, fd: s.FunDef): (t.FunDef, Unit) =
    (context.transform(fd), ())
}

object DispatchFlattening {
  def apply(it: inlining.Trees)(using inox.Context): ExtractionPipeline {
    val s: it.type
    val t: it.type
  } = {
    class Impl(override val s: it.type, override val t: it.type) extends DispatchFlattening(s, t)
    new Impl(it, it)
  }
}
