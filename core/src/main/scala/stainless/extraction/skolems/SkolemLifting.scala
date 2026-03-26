/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package skolems

class SkolemLifting(override val s: Trees, override val t: xlang.Trees)
                      (using override val context: inox.Context)
  extends oo.ExtractionPipeline
     with oo.NoSummaryPhase
     with IdentitySorts
     with SimpleFunctions
     with SimplyCachedFunctions
     with oo.IdentityTypeDefs
     with oo.IdentityClasses { self =>
  override protected type TransformerContext = s.Symbols
  override protected def getContext(symbols: s.Symbols) = symbols

  import s._

  override def extractFunction(context: s.Symbols, fd: s.FunDef): (t.FunDef, Unit) = {

    import context.{given, _}
    class SkolemTransformer(override val s: self.s.type, override val t: self.t.type)
      extends transformers.ConcreteTreeTransformer(s, t) {

      override def transform(e: s.Expr): t.Expr = e match {
        case s.Skolem(id, tpe) =>
          println(s"Krowa id: $id, tpe: $tpe")
          t.NoTree(transform(tpe))
        case _ =>
          super.transform(e)
      }
    }


    val transformer = new SkolemTransformer(self.s, self.t)
    (transformer.transform(fd), ())
  }

}

object SkolemLifting {
  def apply(ts: Trees, tt: xlang.Trees)(using inox.Context): ExtractionPipeline {
    val s: ts.type
    val t: tt.type
  } = {
    class Impl(override val s: ts.type, override val t: tt.type) extends SkolemLifting(s, t)
    new Impl(ts, tt)
  }
}
