/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package frontend

import extraction.xlang.{ trees => xt }

// Always keep library objects marked by @keep(g) for some g in g1,...,gn
object optKeep extends inox.OptionDef[Seq[String]] {
  val name = "keep"
  val default = Seq[String]()
  val parser = inox.OptionParsers.seqParser(inox.OptionParsers.stringParser)
  val usageRhs = "g1,g2,..."
}

/**
 * Process the extracted units.
 *
 * Frontends are required to follow this workflow (== one cycle):
 *  - when starting extracting compilation unit, [[beginExtractions]] should be called once;
 *  - the [[CallBack.apply]] method after extracting each compilation unit (i.e. a Scala file);
 *  - the [[CallBack.failed]] method if the compilation unit extraction failed (or it contained errors);
 *  - finally, the frontend calls [[endExtractions]] to let the CallBack know all the data
 *    should be available by now.
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
  def apply(file: String, unit: xt.UnitDef, classes: Seq[xt.ClassDef], functions: Seq[xt.FunDef]): Unit
  def failed(): Unit
  def endExtractions(): Unit

  def stop(): Unit // Blocking "stop".

  def join(): Unit // Wait until all tasks have finished.

  def getReport: Option[AbstractReport[_]]
}
