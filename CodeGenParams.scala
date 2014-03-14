/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package codegen

case class CodeGenParams (
  maxFunctionInvocations: Int = -1,     // Monitor calls and abort execution if more than X calls
  checkContracts: Boolean = false,      // Generate calls that checks pre/postconditions
  doInstrument: Boolean = true          // Instrument reads to case classes (mainly for vanuatoo)
) {
  val recordInvocations = maxFunctionInvocations > -1

  val requireMonitor = recordInvocations
}
