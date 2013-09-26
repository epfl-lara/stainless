package leon
package codegen

case class CodeGenEvalParams (
  maxFunctionInvocations: Int = -1,
  checkContracts: Boolean = false
)
