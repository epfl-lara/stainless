package leon
package codegen

case class CodeGenParams (
  maxFunctionInvocations: Int = -1,
  checkContracts: Boolean = false

) {
  val recordInvocations = maxFunctionInvocations > -1

  val requireMonitor = recordInvocations
}
