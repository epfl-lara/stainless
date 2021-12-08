/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package inlining

class CallSiteInline(override val s: Trees, override val t: Trees)
                    (using override val context: inox.Context) extends CachingPhase with SimpleFunctions with IdentitySorts { self =>
  import s._

  override protected final val funCache = new ExtractionCache[s.FunDef, FunctionResult]((fd, context) =>
    getDependencyKey(fd.id)(using context.symbols)
  )

  protected class TransformerContext(override val s: self.s.type,
                                     override val t: self.t.type,
                                     val symbols: self.s.Symbols) extends inox.transformers.TreeTransformer {
    def this(symbols: self.s.Symbols) = this(self.s, self.t, symbols)

    import s._
    import symbols.{given, _}

    object InlineCall {
      def unapply(e: Expr): Option[FunctionInvocation] = e match {
        case FunctionInvocation(
          ast.SymbolIdentifier("stainless.lang.inline"),
          Seq(_),
          Seq(fi: FunctionInvocation)
        ) => Some(fi)
        case _ => None
      }
    }

    override def transform(e: Expr): t.Expr = e match {
      case InlineCall(fi) => t.annotated(transform(fi.inlined), t.DropVCs)
      case _ => super.transform(e)
    }

  }

  override protected def getContext(symbols: s.Symbols) = new TransformerContext(symbols)

  def extractFunction(context: TransformerContext, fd: s.FunDef): t.FunDef = {
    context.transform(fd)
  }

}

object CallSiteInline {
  def apply(it: inlining.Trees)(using inox.Context): ExtractionPipeline {
    val s: it.type
    val t: it.type
  } = {
    class Impl(override val s: it.type, override val t: it.type) extends CallSiteInline(s, t)
    new Impl(it, it)
  }
}
