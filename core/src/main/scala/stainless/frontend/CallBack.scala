/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package frontend

import extraction.xlang.{ trees => xt }

// Keep library objects marked by @keepFor(g) for some g in g1,...,gn
object optKeep extends inox.OptionDef[Seq[String]] {
  val name = "keep"
  val default = Seq[String]()
  val parser = inox.OptionParsers.seqParser(inox.OptionParsers.stringParser)
  val usageRhs = "g1,g2,..."
}

/**
 * Process the extracted units.
 *
 * During a cycle, a [[Frontend]] should call:
 *  - [[CallBack.beginExtractions]] once before starting any extraction,
 *  - [[CallBack.apply]] for each compilation unit that is extracted succeffuly,
 *  - [[CallBack.endExtractions]] once after all extractions are done, whereas
 *    there has been errors or not during the extractions.
 *
 * A compilation unit usually corresponds to one Scala file.
 *
 * When a compilation unit is recompiled, the callback deals with any potential invalidation of
 * existing data without blocking the callee's thread.
 *
 * A [[Frontend]] has to [[stop]] or [[join]] its callback at some point between two cycles.
 * A callback cannot be reused after calling [[stop]].
 *
 * Calling [[getReport]] is valid exclusively after [[join]]ing and before the next cycle starts.
 *
 * A callback is expected to be used by only one frontend at a time.
 */
trait CallBack {
  def beginExtractions(): Unit
  def apply(file: String, unit: xt.UnitDef, classes: Seq[xt.ClassDef], functions: Seq[xt.FunDef], typeDefs: Seq[xt.TypeDef]): Unit
  def endExtractions(): Unit

  def stop(): Unit // Blocking "stop".

  def join(): Unit // Wait until all tasks have finished.

  def getReport: Option[AbstractReport[?]]
}
