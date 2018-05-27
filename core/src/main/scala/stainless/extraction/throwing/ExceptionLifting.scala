/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package throwing

trait ExceptionLifting extends oo.SimplePhase { self =>
  val s: Trees
  val t: ast.Trees
}

object ExceptionLifting {
  def apply(ts: Trees, tt: ast.Trees)(implicit ctx: inox.Context): ExtractionPipeline {
    val s: ts.type
    val t: tt.type
  } = new ExceptionLifting {
    override val s: ts.type = ts
    override val t: tt.type = tt
    override val context = ctx
  }
}
