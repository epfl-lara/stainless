/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package throwing

class ExceptionLifting(override val s: Trees, override val t: imperative.Trees)
                      (using override val context: inox.Context)
  extends oo.ExtractionPipeline
     with IdentityFunctions
     with IdentitySorts
     with oo.IdentityTypeDefs
     with oo.IdentityClasses { self =>
  override protected type TransformerContext = s.Symbols
  override protected def getContext(symbols: s.Symbols) = symbols
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
