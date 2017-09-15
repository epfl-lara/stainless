/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package termination

import inox.utils.ASCIIHelpers._
import stainless.utils.JsonConvertions._

import org.json4s.JsonDSL._
import org.json4s.JsonAST._

object TerminationReport {

  sealed abstract class Status {
    def isUnknown = this == Unknown
    def isTerminating = this == Terminating
    def isNonTerminating = this == NonTerminating

    def toText = this match {
      case Unknown => "unknown"
      case Terminating => "terminating"
      case NonTerminating => "non-terminating"
    }
  }

  object Status {
    def parse(json: JValue) = json match {
      case JString("unknown") => Unknown
      case JString("terminating") => Terminating
      case JString("non-terminating") => NonTerminating
      case _ => ???
    }
  }

  case object Unknown extends Status
  case object Terminating extends Status
  case object NonTerminating extends Status

  case class Record(
    fid: Identifier, pos: inox.utils.Position, time: Long,
    status: Status, verdict: String, kind: String
  )

  def parse(json: JValue): TerminationReport = {
    val records = for {
      JArray(records) <- json
      record <- records
    } yield {
      val fid = parseIdentifier(record \ "_fid")
      val pos = parsePosition(record \ "pos")
      val JInt(time) = record \ "time"
      val JString(kind) = record \ "kind"
      val JString(verdict) = record \ "verdict"
      val status = Status.parse(record \ "status")

      Record(fid, pos, time.longValue, status, verdict, kind)
    }

    new TerminationReport(records)
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

  override def emitJson: JArray = for { Record(fid, pos, time, status, verdict, kind) <- results } yield {
    ("fd" -> fid.name) ~
    ("_fid" -> fid.toJson) ~
    ("pos" -> pos.toJson) ~
    ("kind" -> kind) ~ // brief
    ("verdict" -> verdict) ~ // detailed
    ("status" -> status.toText) ~
    ("time" -> time)
  }

}

