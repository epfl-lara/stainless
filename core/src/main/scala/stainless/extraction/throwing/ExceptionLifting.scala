/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package throwing

trait ExceptionLifting extends PipelinePhase with SimpleOOPhase { self =>
  val s: Trees
  val t: ast.Trees
}

object ExceptionLifting {
  def apply(ts: Trees, tt: ast.Trees)(prev: ExtractionPhase { val t: ts.type }): ExtractionPhase {
    val s: ts.type
    val t: tt.type
  } = new ExceptionLifting {
    override val s: ts.type = ts
    override val t: tt.type = tt
    override protected val previous: prev.type = prev
  }
}
