/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package frontend

import extraction.xlang.{ trees => xt }

/**
 * Process the extracted units.
 *
 * Frontends are required to call the [[CallBack.apply]] method after extracting
 * each compilation unit (i.e. a scala file). When a compilation unit is recompiled, the
 * callback deals with any potential invalidation of existing data without blocking the
 * callee's thread.
 *
 * A [[Frontend]] has to [[stop]] or [[join]] its callback at some point.
 *
 * Calling [[getReports]] is valid if and only if:
 *  - the callback has been joined, and
 *  - the program was not running in "watch" mode.
 */
trait CallBack {
  // TODO maybe file and unit are not required and should be removed.
  def apply(file: String, unit: xt.UnitDef, classes: Seq[xt.ClassDef], functions: Seq[xt.FunDef]): Unit

  def stop(): Unit // Blocking "stop".

  def join(): Unit // Wait until all tasks have finished.

  def getReports: Seq[AbstractReport]
}

/** MasterCallBack: combine several callbacks together. */
class MasterCallBack(val callbacks: Seq[CallBack]) extends CallBack {
  override def apply(file: String, unit: xt.UnitDef,
                     classes: Seq[xt.ClassDef], functions: Seq[xt.FunDef]): Unit = {
    callbacks foreach { c => c(file, unit, classes, functions) }
  }

  override def stop(): Unit = callbacks foreach { _.stop() }

  override def join(): Unit = callbacks foreach { _.join() }

  override def getReports: Seq[AbstractReport] = callbacks flatMap { _.getReports }
}

