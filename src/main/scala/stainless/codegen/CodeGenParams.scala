/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package codegen

case class CodeGenParams (
  maxFunctionInvocations: Int,     // Monitor calls and abort execution if more than X calls
  checkContracts: Boolean,         // Generate calls that checks pre/postconditions
  doInstrument: Boolean            // Instrument reads to case classes (mainly for vanuatoo)
) {
  val recordInvocations = maxFunctionInvocations > -1

  val requireMonitor = recordInvocations
}

object CodeGenParams {
  def default = CodeGenParams(maxFunctionInvocations = -1, checkContracts = true, doInstrument = false)
}
