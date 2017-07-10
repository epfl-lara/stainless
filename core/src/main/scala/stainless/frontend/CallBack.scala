/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package frontend

import extraction.xlang.{ trees => xt }

/**
 * Process the extracted units.
 *
 * Frontends are required to follow this workflow:
 *  - when starting extracting compilation unit, [[beginExtractions]] should be called once;
 *  - the [[CallBack.apply]] method after extracting each compilation unit (i.e. a scala file);
 *  - finally, the frontend calls [[endExtractions]] to let the CallBack know all the data
 *    should be available by now.
 *
 * When a compilation unit is recompiled, the callback deals with any potential invalidation of
 * existing data without blocking the callee's thread.
 *
 * A [[Frontend]] has to [[stop]] or [[join]] its callback at some point.
 *
 * Calling [[getReports]] is valid if and only if:
 *  - the callback has been joined, and
 *  - the program was not running in "watch" mode.
 *
 * NOTE A callback is expected to be used by only one frontend at a time.
 */
trait CallBack {
  def beginExtractions(): Unit
  def apply(file: String, unit: xt.UnitDef, classes: Seq[xt.ClassDef], functions: Seq[xt.FunDef]): Unit
  def endExtractions(): Unit

  def stop(): Unit // Blocking "stop".

  def join(): Unit // Wait until all tasks have finished.

  def getReports: Seq[AbstractReport]
}

/** MasterCallBack: combine several callbacks together. */
class MasterCallBack(val callbacks: Seq[CallBack]) extends CallBack {
  override def beginExtractions(): Unit = callbacks foreach { _.beginExtractions() }

  override def apply(file: String, unit: xt.UnitDef,
                     classes: Seq[xt.ClassDef], functions: Seq[xt.FunDef]): Unit = {
    callbacks foreach { c => c(file, unit, classes, functions) }
  }

  override def endExtractions(): Unit = callbacks foreach { _.endExtractions() }

  override def stop(): Unit = callbacks foreach { _.stop() }

  override def join(): Unit = callbacks foreach { _.join() }

  // Group together reports from the same callback
  override def getReports: Seq[AbstractReport] = callbacks flatMap { c =>
    val inners = c.getReports
    if (inners.isEmpty) None
    else Some(inners reduce { _ ~ _ })
  }
}

