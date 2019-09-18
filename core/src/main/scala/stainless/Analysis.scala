/* Copyright 2009-2019 EPFL, Lausanne */

package stainless

/**
 * Analyses hold all the information about a [[Component]] results.
 *
 * They can be converted to basic, text-only report, which can be easily serialized or displayed to the user,
 * or they can be used, when their concrete type is known, to explore in detail the results of components,
 * such as the source program itself.
 */
trait AbstractAnalysis {
  val name: String

  type Report <: AbstractReport[Report]

  def toReport: Report
}

