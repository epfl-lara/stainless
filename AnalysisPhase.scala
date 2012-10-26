package leon
package verification

import purescala.Definitions._

object AnalysisPhase extends UnitPhase[Program] {
  val name = "Analysis"
  val description = "Leon Analyses"

  def apply(ctx: LeonContext, program: Program) {
    new Analysis(program, ctx.reporter).analyse
  }
}
