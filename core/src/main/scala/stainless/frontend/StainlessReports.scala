/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package frontend

import io.circe._
import io.circe.syntax._

trait StainlessReports {
  protected trait RunReport { val run: ComponentRun; val report: run.component.Report }
  protected def RunReport(r: ComponentRun)(re: r.component.Report): RunReport { val run: r.type; val report: re.type } =
    new RunReport { val run: r.type = r; val report: re.type = re }

  protected case class Report(reports: Seq[RunReport]) extends AbstractReport[Report] {
    val name = "stainless"

    override def ~(other: Report): Report = Report(
      (reports ++ other.reports).groupBy(_.run).map {
        case (run, reports) => RunReport(run)(reports.map(_.report.asInstanceOf[run.component.Report]) reduce (_ ~ _))
      }.toSeq
    )

    override lazy val annotatedRows = reports.flatMap(_.report.annotatedRows: Seq[RecordRow])

    override def emitJson = reports.map(rr => rr.run.component.name -> rr.report.emitJson).asJson

    override def filter(ids: Set[Identifier]): Report =
      Report(reports.map(rr => RunReport(rr.run)(rr.report filter ids)))

    override lazy val stats: stainless.ReportStats = {
      val reportStats = reports.map(_.report.stats)
      ReportStats(
        reportStats.map(_.total         ).sum,
        reportStats.map(_.time          ).sum,
        reportStats.map(_.valid         ).sum,
        reportStats.map(_.validFromCache).sum,
        reportStats.map(_.invalid       ).sum,
        reportStats.map(_.unknown       ).sum)
    }
  }

}