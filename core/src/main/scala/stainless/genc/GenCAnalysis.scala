/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package genc

import extraction.xlang.trees as xt
import stainless.extraction.ExtractionSummary

trait GenCAnalysis extends AbstractAnalysis {
  import GenCRun.Result
  import GenCReport.Record

  val program: Program { val trees: xt.type }
  val sources: Set[Identifier] // set of functions that were considered for the analysis
  val results: Seq[Result]
  val extractionSummary: ExtractionSummary

  private lazy val records = results map { case Result(fd, status, time) =>
    Record(fd.id, fd.getPos, status, time)
  }

  override type Report = GenCReport
  override val name = GenCComponent.name
  override def toReport = new GenCReport(records, sources, extractionSummary)
}
