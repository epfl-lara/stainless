package leon.verification

import leon.purescala.Trees._
import leon.purescala.Definitions._
import leon.purescala.Common._

import leon.solvers.Solver

/** This is just to hold some history information. */
class VerificationCondition(val condition: Expr, val funDef: FunDef, val kind: VCKind.Value, val tactic: Tactic, val info: String = "") extends ScalacPositional {
  // None = still unknown
  // Some(true) = valid
  // Some(false) = valid
  var value : Option[Boolean] = None
  var solvedWith : Option[Solver] = None
  var time : Option[Double] = None

  def status : String = value match {
    case None => "unknown"
    case Some(true) => "valid"
    case Some(false) => "invalid"
  }

  private def tacticStr = tactic.shortDescription match {
    case "default" => ""
    case s => s
  }

  private def solverStr = solvedWith match {
    case Some(s) => s.shortDescription
    case None => ""
  }

  private def timeStr = time.map(t => "%-3.3f".format(t)).getOrElse("")

  def infoLine : String = {
    "║ %-25s %-9s %9s %-8s %-10s %-7s %7s ║" format (funDef.id.toString, kind, posInfo, status, tacticStr, solverStr, timeStr)
  }
}

object VerificationCondition {
  val infoFooter : String = "╚" + ("═" * 83) + "╝"
  val infoHeader : String = ". ┌─────────┐\n" +
                            "╔═╡ Summary ╞" + ("═" * 71) + "╗\n" +
                            "║ └─────────┘" + (" " * 71) + "║"
}

object VCKind extends Enumeration {
  val Precondition = Value("precond.")
  val Postcondition = Value("postcond.")
  val ExhaustiveMatch = Value("match.")
  val MapAccess = Value("map acc.")
  val ArrayAccess = Value("arr. acc.")
  val InvariantInit = Value("inv init.")
  val InvariantInd = Value("inv ind.")
  val InvariantPost = Value("inv post.")
}
