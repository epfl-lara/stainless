/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package frontend

import io.circe._
import io.circe.syntax._
import stainless.extraction.ExtractionSummary

trait StainlessReports {
  trait RunReport { val run: ComponentRun; val report: run.component.Report }
  def RunReport(r: ComponentRun)(re: r.component.Report): RunReport { val run: r.type; val report: re.type } =
    new RunReport { val run: r.type = r; val report: re.type = re }

  case class Report(reports: Seq[RunReport]) extends AbstractReport[Report] {
    val name = "stainless"

    override lazy val extractionSummary: ExtractionSummary = reports.foldLeft(ExtractionSummary.NoSummary) {
      case (acc, report) => ExtractionSummary.Node(acc, report.report.extractionSummary)
    }

    override def ~(other: Report): Report = Report(
      (reports ++ other.reports).groupBy(_.run).map {
        case (run, reports) => RunReport(run)(reports.map(_.report.asInstanceOf[run.component.Report]) reduce (_ ~ _))
      }.toSeq
    )

    override lazy val annotatedRows = adjustRows(reports)

    override def emitJson = reports.map(rr => rr.run.component.name -> rr.report.emitJson).asJson

    override def filter(ids: Set[Identifier]): Report =
      Report(reports.map(rr => RunReport(rr.run)(rr.report `filter` ids)))

    override lazy val stats: stainless.ReportStats = {
      val reportStats = reports.map(_.report.stats)
      ReportStats(
        reportStats.map(_.total         ).sum,
        reportStats.map(_.time          ).sum,
        reportStats.map(_.valid         ).sum,
        reportStats.map(_.validFromCache).sum,
        reportStats.map(_.trivial       ).sum,
        reportStats.map(_.invalid       ).sum,
        reportStats.map(_.unknown       ).sum)
    }
  }

  private def adjustRows(reports: Seq[RunReport]): Seq[RecordRow] = {
    val maxExtra = reports
      .flatMap(_.report.annotatedRows)
      .foldLeft(0) { case (max, row) => Math.max(max, row.extra.size) }

    reports flatMap { re =>
      re.report.annotatedRows map { row =>
        row.copy(extra = row.extra ++ Seq.fill(maxExtra - row.extra.size)(""))
      }
    }
  }
}
