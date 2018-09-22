/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package throwing

trait ExceptionLifting
  extends oo.ExtractionPipeline
     with IdentityFunctions
     with IdentitySorts
     with oo.IdentityClasses { self =>

  val s: Trees
  val t: oo.Trees

  override protected type TransformerContext = s.Symbols
  override protected def getContext(symbols: s.Symbols) = symbols
}

object ExceptionLifting {
  def apply(ts: Trees, tt: oo.Trees)(implicit ctx: inox.Context): ExtractionPipeline {
    val s: ts.type
    val t: tt.type
  } = new ExceptionLifting {
    override val s: ts.type = ts
    override val t: tt.type = tt
    override val context = ctx
  }
}
