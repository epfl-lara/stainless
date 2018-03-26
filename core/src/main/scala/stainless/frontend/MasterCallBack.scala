/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package frontend

import extraction.xlang.{ trees => xt }

/**
 * MasterCallBack: combine several callbacks together.
 *
 * The interface is similar to [[CallBack]], except for the [[getReports]]
 * method which returns one [[AbstractReport]] per active component.
 *
 * Otherwise, the same consideration applies to its API.
 */
final class MasterCallBack(val callbacks: Seq[CallBack]) {
  def beginExtractions(): Unit = callbacks foreach { _.beginExtractions() }

  def apply(file: String, unit: xt.UnitDef, classes: Seq[xt.ClassDef], functions: Seq[xt.FunDef]): Unit = {
    callbacks foreach { c => c(file, unit, classes, functions) }
  }

  def endExtractions(): Unit = callbacks foreach { _.endExtractions() }

  def stop(): Unit = callbacks foreach { _.stop() }

  def join(): Unit = callbacks foreach { _.join() }

  // Group together reports from the same callback
  def getReports: Seq[AbstractReport[_]] = callbacks flatMap { _.getReport }
}

