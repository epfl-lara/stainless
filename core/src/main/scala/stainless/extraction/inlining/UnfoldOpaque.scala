/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package inlining

class UnfoldOpaque(override val s: Trees, override val t: Trees)
                  (using override val context: inox.Context) extends CachingPhase with SimpleFunctions with IdentitySorts { self =>

  override protected final val funCache = new ExtractionCache[s.FunDef, FunctionResult]((fd, context) =>
    getDependencyKey(fd.id)(using context.symbols)
  )

  protected class TransformerContext(override val s: self.s.type,
                                     override val t: self.t.type,
                                     val symbols: self.s.Symbols) extends inox.transformers.TreeTransformer {
    def this(symbols: self.s.Symbols) = this(self.s, self.t, symbols)

    import s._
    import symbols.{given, _}

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
  def apply(it: inlining.Trees)(using inox.Context): ExtractionPipeline {
    val s: it.type
    val t: it.type
  } = {
    class Impl(override val s: it.type, override val t: it.type) extends UnfoldOpaque(s, t)
    new Impl(it, it)
  }
}
