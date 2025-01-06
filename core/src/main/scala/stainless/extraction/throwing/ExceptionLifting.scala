/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package throwing

class ExceptionLifting(override val s: Trees, override val t: imperative.Trees)
                      (using override val context: inox.Context)
  extends oo.ExtractionPipeline
     with oo.NoSummaryPhase
     with IdentityFunctions
     with IdentitySorts
     with oo.IdentityTypeDefs
     with oo.IdentityClasses { self =>
  override protected type TransformerContext = s.Symbols
  override protected def getContext(symbols: s.Symbols) = symbols

  import s._

  private class ThrowingIdentityImpl(override val s: self.s.type, override val t: self.t.type)
    extends transformers.ConcreteTreeTransformer(s, t)

  private val identity = new ThrowingIdentityImpl(self.s, self.t)

  override def extractFunction(context: s.Symbols, fd: s.FunDef): (t.FunDef, Unit) = {
    import context.{given, _}

    class ThrowTransformer(override val s: self.s.type, override val t: self.t.type)
      extends transformers.ConcreteTreeTransformer(s, t) {
      transSelf =>

      override def transform(e: s.Expr): t.Expr = e match {
        case s.Throw(exc) =>
          t.Assert(t.BooleanLiteral(false).setPos(e), Some(f"throw $exc unreachable"), t.NoTree(transform(fd.returnType)).setPos(e)).setPos(e)
        case _ =>
          super.transform(e)
      }
    }


    val throwTransformer = new ThrowTransformer(self.s, self.t)
    (throwTransformer.transform(fd.copy(
      fullBody = fd.fullBody,
      flags = fd.flags
    )), ())

  }

}

object ExceptionLifting {
  def apply(ts: Trees, tt: imperative.Trees)(using inox.Context): ExtractionPipeline {
    val s: ts.type
    val t: tt.type
  } = {
    class Impl(override val s: ts.type, override val t: tt.type) extends ExceptionLifting(s, t)
    new Impl(ts, tt)
  }
}
