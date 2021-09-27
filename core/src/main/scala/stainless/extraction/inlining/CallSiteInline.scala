/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package inlining

trait CallSiteInline extends CachingPhase with SimpleFunctions with IdentitySorts { self =>

  implicit val context: inox.Context
  val s: Trees
  val t: Trees
  import s._

  override protected final val funCache = new ExtractionCache[s.FunDef, FunctionResult]((fd, context) =>
    getDependencyKey(fd.id)(context.symbols)
  )


  protected class TransformerContext(val symbols: s.Symbols) extends inox.transformers.TreeTransformer {
    override final val s: self.s.type = self.s
    override final val t: self.t.type = self.t

    import s._
    import symbols._

    object SpecializeCall {
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
      case SpecializeCall(fi) => transform(fi.inlined)
      case _ => super.transform(e)
    }

  }

  override protected def getContext(symbols: s.Symbols) = new TransformerContext(symbols)

  def extractFunction(context: TransformerContext, fd: s.FunDef): t.FunDef = {
    context.transform(fd)
  }

}

object CallSiteInline {
  def apply(it: inlining.Trees)(implicit ctx: inox.Context): ExtractionPipeline {
    val s: it.type
    val t: it.type
  } = new CallSiteInline {
    override val context = ctx
    override val s: it.type = it
    override val t: it.type = it
  }
}
