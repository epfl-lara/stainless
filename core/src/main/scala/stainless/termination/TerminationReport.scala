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
    fid: Identifier, pos: inox.utils.Position, time: Long,
    status: Status, verdict: String, kind: String
  )

  implicit val recordDecoder: Decoder[Record] = deriveDecoder
  implicit val recordEncoder: Encoder[Record] = deriveEncoder

  def parse(json: Json): TerminationReport = json.as[Seq[Record]] match {
    case Right(records) => new TerminationReport(records)
    case Left(error) => throw error
  }

}

// Variant of the report without the checker, where all the data is mapped to text
class TerminationReport(val results: Seq[TerminationReport.Record]) extends AbstractReport[TerminationReport] {
  import TerminationReport._

  override val name: String = TerminationComponent.name

  override def ~(other: TerminationReport): TerminationReport = {
    def buildMapping(subs: Seq[Record]): Map[Identifier, Seq[Record]] = subs groupBy { _.fid }

    val prev = buildMapping(this.results)
    val next = buildMapping(other.results)

    val fused = (prev ++ next).values.fold(Seq.empty)(_ ++ _)

    new TerminationReport(results = fused)
  }

  override def invalidate(ids: Seq[Identifier]) =
    new TerminationReport(results filterNot { ids contains _.fid })

  override def emitRowsAndStats: Option[(Seq[Row], ReportStats)] = if (results.isEmpty) None else {
    val rows = for { Record(fid, pos, time, status, verdict, kind) <- results } yield Row(Seq(
      Cell(fid.name),
      Cell((if (status.isTerminating) "\u2713" else "\u2717") + " " + verdict),
      Cell(f"${time / 1000d}%3.3f")
    ))

    val valid = results count { _.status.isTerminating }
    val validFromCache = 0
    val invalid = results count { _.status.isNonTerminating }
    val unknown = results count { _.status.isUnknown }
    val time = (results map { _.time }).sum

    val stats = ReportStats(results.size, time, valid, validFromCache, invalid, unknown)

    Some((rows, stats))
  }

  override def emitJson: Json = results.asJson

}

