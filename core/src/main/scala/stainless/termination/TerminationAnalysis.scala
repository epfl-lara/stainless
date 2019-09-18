/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package termination

trait TerminationAnalysis extends AbstractAnalysis {
  val checker: TerminationChecker {
    val program: TerminationProgram
  }

  import checker._
  import context._
  import program._
  import program.trees._

  type Duration = Long
  type Record = (TerminationGuarantee, Duration)
  val results: Map[FunDef, Record]
  val sources: Set[Identifier] // set of functions that were considered for the analysis

  override val name: String = TerminationComponent.name

  override type Report = TerminationReport

  override def toReport = new TerminationReport(records, sources)

  private lazy val records = results.toSeq map { case (fd, (g, time)) =>
    TerminationReport.Record(fd.id, fd.getPos, time, status(g), verdict(g), derivedFrom = fd.source)
  }

  private def verdict(g: TerminationGuarantee): String = g match {
    case checker.NotWellFormed(_) => "ill-formed"
    case checker.LoopsGivenInputs(_) => "non-terminating loop"
    case checker.MaybeLoopsGivenInputs(_) => "possibly non-terminating loop"
    case checker.CallsNonTerminating(_) => "non-terminating call"
    case checker.DecreasesFailed(_) => "failed decreases check"
    case checker.Terminates(_) => "terminates"
    case checker.NoGuarantee => "no guarantee"
  }

  private def status(g: TerminationGuarantee): TerminationReport.Status = g match {
    case checker.NoGuarantee => TerminationReport.Unknown
    case checker.Terminates(_) => TerminationReport.Terminating
    case _ => TerminationReport.NonTerminating
  }

}

