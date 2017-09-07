/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package frontend

import extraction.xlang.{ trees => xt }

/**
 * Process the extracted units.
 *
 * Frontends are required to follow this workflow (== one cycle):
 *  - when starting extracting compilation unit, [[beginExtractions]] should be called once;
 *  - the [[CallBack.apply]] method after extracting each compilation unit (i.e. a Scala file);
 *  - finally, the frontend calls [[endExtractions]] to let the CallBack know all the data
 *    should be available by now.
 *
 * When a compilation unit is recompiled, the callback deals with any potential invalidation of
 * existing data without blocking the callee's thread.
 *
 * A [[Frontend]] has to [[stop]] or [[join]] its callback at some point between two cycles.
 * A callback cannot be reused after calling [[stop]].
 *
 * Calling [[getReports]] is valid exclusively after [[join]]ing and before the next cycle starts.
 *
 * A callback is expected to be used by only one frontend at a time.
 */
trait CallBack {
  def beginExtractions(): Unit
  def apply(file: String, unit: xt.UnitDef, classes: Seq[xt.ClassDef], functions: Seq[xt.FunDef]): Unit
  def endExtractions(): Unit

  def stop(): Unit // Blocking "stop".

  def join(): Unit // Wait until all tasks have finished.

  def getReports: Seq[AbstractReport[_]]
}


/** MasterCallBack: combine several callbacks together. */
final class MasterCallBack(val callbacks: Seq[CallBack]) extends CallBack {
  override def beginExtractions(): Unit = callbacks foreach { _.beginExtractions() }

  override def apply(file: String, unit: xt.UnitDef,
                     classes: Seq[xt.ClassDef], functions: Seq[xt.FunDef]): Unit = {
    callbacks foreach { c => c(file, unit, classes, functions) }
  }

  override def endExtractions(): Unit = callbacks foreach { _.endExtractions() }

  override def stop(): Unit = callbacks foreach { _.stop() }

  override def join(): Unit = callbacks foreach { _.join() }

  // Group together reports from the same callback
  override def getReports: Seq[AbstractReport[_]] = callbacks flatMap { _.getReports }
}
