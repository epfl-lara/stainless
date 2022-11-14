/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package termination

import stainless.extraction.ExtractionSummary

trait TerminationAnalysis extends AbstractAnalysis {
  val program: Program

  import program._
  import program.trees._

  type Duration = Long
  type Record = TerminationReport.Status

  val results: Map[FunDef, Record]
  val sources: Set[Identifier] // set of functions that were considered for the analysis
  val extractionSummary: ExtractionSummary

  override val name: String = TerminationComponent.name

  override type Report = TerminationReport

  override def toReport = new TerminationReport(records, sources, extractionSummary)

  private lazy val records = results.toSeq map { case (fd, status) =>
    TerminationReport.Record(fd.id, fd.getPos, status, derivedFrom = fd.source)
  }
}
