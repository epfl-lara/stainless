/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package inlining

trait UnfoldOpaque extends CachingPhase with SimpleFunctions with IdentitySorts { self =>

  implicit val context: inox.Context
  val s: Trees
  val t: Trees

  override protected final val funCache = new ExtractionCache[s.FunDef, FunctionResult]((fd, context) =>
    getDependencyKey(fd.id)(context.symbols)
  )

  protected class TransformerContext(val symbols: s.Symbols) extends inox.transformers.TreeTransformer {
    override final val s: self.s.type = self.s
    override final val t: self.t.type = self.t

    import s._
    import symbols._

    object UnfoldOpaque {
      def unapply(e: s.Expr): Option[s.FunctionInvocation] = e match {
        case s.FunctionInvocation(
          ast.SymbolIdentifier("stainless.lang.unfold"),
          Seq(_),
          Seq(fi: s.FunctionInvocation)
        ) => Some(fi)
        case _ => None
      }
    }

    override def transform(e: Expr): t.Expr = e match {
      case UnfoldOpaque(fi) =>
        val newFi = transform(fi)
        val inlined = transform(fi.inlined)
        val specced = t.exprOps.BodyWithSpecs(inlined)
        t.Assume(t.Equals(newFi, t.annotated(specced.letsAndBody, t.DropVCs)).setPos(e), t.UnitLiteral().setPos(e)).setPos(e)
      case _ => super.transform(e)
    }

  }

  override protected def getContext(symbols: s.Symbols) = new TransformerContext(symbols)

  def extractFunction(context: TransformerContext, fd: s.FunDef): t.FunDef = {
    context.transform(fd)
  }

}

object UnfoldOpaque {
  def apply(it: inlining.Trees)(implicit ctx: inox.Context): ExtractionPipeline {
    val s: it.type
    val t: it.type
  } = new UnfoldOpaque {
    override val context = ctx
    override val s: it.type = it
    override val t: it.type = it
  }
}
