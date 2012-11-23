package leon
package verification

import purescala.Definitions._

object AnalysisPhase extends LeonPhase[Program,VerificationReport] {
  val name = "Analysis"
  val description = "Leon Verification"

  override def definedOptions = Set(
    LeonFlagOptionDef("no-luck", "--no-luck", "Disable early model detection in solving loop.")
  )

  def run(ctx: LeonContext)(program: Program) : VerificationReport = {
    new Analysis(program, ctx.reporter).analyse
  }
}
