/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package termination

import inox.utils.ASCIIHelpers.{ Cell, Row }
import stainless.utils.JsonConvertions.given

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

  given statusDecoder: Decoder[Status] = deriveDecoder
  given statusEncoder: Encoder[Status] = deriveEncoder

  case class Record(
    id: Identifier,
    pos: inox.utils.Position,
    status: Status,
    derivedFrom: Identifier
  ) extends AbstractReportHelper.Record

  given recordDecoder: Decoder[Record] = deriveDecoder
  given recordEncoder: Encoder[Record] = deriveEncoder

  def parse(json: Json) = json.as[(Seq[Record], Set[Identifier])] match {
    case Right((records, sources)) => new TerminationReport(records, sources)
    case Left(error) => throw error
  }

}

// Variant of the report without the checker, where all the data is mapped to text
class TerminationReport(val results: Seq[TerminationReport.Record], val sources: Set[Identifier])
  extends BuildableAbstractReport[TerminationReport.Record, TerminationReport] {
  import TerminationReport.{given, _}

  override val encoder = recordEncoder

  override def build(results: Seq[Record], sources: Set[Identifier]) =
    new TerminationReport(results, sources)

  override val name: String = TerminationComponent.name

  lazy val totalValid          = results count { _.status.isTerminating }
  lazy val totalValidFromCache = 0
  lazy val totalInvalid        = results count { _.status.isNonTerminating }
  lazy val totalUnknown        = results count { _.status.isUnknown }

  override lazy val annotatedRows = results map {
    case Record(id, pos, status, _) =>
      val level  = levelOf(status)
      val symbol = if (status.isTerminating) "\u2713" else "\u2717"
      val extra  = Seq(s"$symbol")

      RecordRow(id, pos, level, extra, 0L)
  }

  private def levelOf(status: Status) = status match {
    case Terminating    => Level.Normal
    case Unknown        => Level.Warning
    case NonTerminating => Level.Error
  }

  override lazy val stats =
    ReportStats(results.size, 0L, totalValid, totalValidFromCache, totalInvalid, totalUnknown)

}
