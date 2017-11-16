/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package termination

import inox.utils.ASCIIHelpers.{ Cell, Row }
import stainless.utils.JsonConvertions._

import io.circe._
import io.circe.syntax._
import io.circe.generic.semiauto._

import scala.util.{ Right, Left }

object TerminationReport {

  sealed abstract class Status {
    def isUnknown = this == Unknown
    def isTerminating = this == Terminating
    def isNonTerminating = this == NonTerminating
  }

  case object Unknown extends Status
  case object Terminating extends Status
  case object NonTerminating extends Status

  implicit val statusDecoder: Decoder[Status] = deriveDecoder
  implicit val statusEncoder: Encoder[Status] = deriveEncoder

  case class Record(
    id: Identifier, pos: inox.utils.Position, time: Long,
    status: Status, verdict: String, kind: String,
    derivedFrom: Identifier
  ) extends AbstractReportHelper.Record

  implicit val recordDecoder: Decoder[Record] = deriveDecoder
  implicit val recordEncoder: Encoder[Record] = deriveEncoder

  def parse(json: Json): TerminationReport = json.as[Seq[Record]] match {
    case Right(records) => new TerminationReport(records)
    case Left(error) => throw error
  }

}

// Variant of the report without the checker, where all the data is mapped to text
class TerminationReport(val results: Seq[TerminationReport.Record])
  extends AbstractReport[TerminationReport] {
  import TerminationReport._

  override val name: String = TerminationComponent.name

  lazy val totalValid = results count { _.status.isTerminating }
  lazy val totalValidFromCache = 0
  lazy val totalInvalid = results count { _.status.isNonTerminating }
  lazy val totalUnknown = results count { _.status.isUnknown }
  lazy val totalTime = (results map { _.time }).sum

  override def ~(other: TerminationReport) =
    new TerminationReport(AbstractReportHelper.merge(this.results, other.results))

  override def filter(ids: Set[Identifier]) =
    new TerminationReport(AbstractReportHelper.filter(results, ids))

  override lazy val annotatedRows = results map {
    case Record(id, pos, time, status, verdict, kind, _) =>
      val level = levelOf(status)
      val symbol = if (status.isTerminating) "\u2713" else "\u2717"
      val extra = Seq(s"$symbol $verdict")

      RecordRow(id, pos, level, extra, time)
  }

  private def levelOf(status: Status) = status match {
    case Terminating => Level.Normal
    case Unknown => Level.Warning
    case NonTerminating => Level.Error
  }

  override lazy val stats =
    ReportStats(results.size, totalTime, totalValid, totalValidFromCache, totalInvalid, totalUnknown)

  override def emitJson: Json = results.asJson

}

