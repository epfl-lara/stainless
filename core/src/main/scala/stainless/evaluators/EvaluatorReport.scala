/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package evaluators

import stainless.utils.JsonConvertions.given

import io.circe._
import io.circe.syntax._
import io.circe.generic.semiauto._

object EvaluatorReport {

  sealed abstract class Status
  case class BodyFailed(error: String) extends Status
  case class PostFailed(bodyValue: String, error: String) extends Status
  case class PostInvalid(bodyValue: String) extends Status
  case class PostHeld(bodyValue: String) extends Status
  case class NoPost(bodyValue: String) extends Status

  given statusDecoder: Decoder[Status] = deriveDecoder
  given statusEncoder: Encoder[Status] = deriveEncoder

  /**
   * Hold the information relative to the evaluation of a function.
   *
   * [[id]]: function's identifier
   * [[pos]]: function's position
   * [[status]]: result of the evaluation, see above
   * [[time]]: amount of time that the evaluation took
   */
  case class Record(id: Identifier, pos: inox.utils.Position, status: Status, time: Long)
    extends AbstractReportHelper.Record {
    override val derivedFrom = id
  }

  given recordDecoder: Decoder[Record] = deriveDecoder
  given recordEncoder: Encoder[Record] = deriveEncoder

  def parse(json: Json) = json.as[(Seq[Record], Set[Identifier])] match {
    case Right((records, sources)) => new EvaluatorReport(records, sources)
    case Left(error) => throw error
  }
}

class EvaluatorReport(val results: Seq[EvaluatorReport.Record], val sources: Set[Identifier])
  extends BuildableAbstractReport[EvaluatorReport.Record, EvaluatorReport] {
  import EvaluatorReport.{given, _}

  override val encoder = recordEncoder

  override def build(results: Seq[Record], sources: Set[Identifier]) =
    new EvaluatorReport(results, sources)

  override val name = EvaluatorComponent.name

  override lazy val annotatedRows = results map {
    case Record(id, pos, status, time) =>
      RecordRow(id, pos, levelOf(status), Seq(descriptionOf(status)), time)
  }

  private lazy val totalTime = (results map { _.time }).sum
  private lazy val totalValid = results count { r => levelOf(r.status) == Level.Normal }
  private lazy val totalInvalid = results.size - totalValid

  override lazy val stats =
    ReportStats(results.size, totalTime, totalValid, validFromCache = 0, totalInvalid, unknown = 0)

  private def levelOf(status: Status) = status match {
    case PostHeld(_) | NoPost(_) => Level.Normal
    case _ => Level.Error
  }

  private def descriptionOf(status: Status): String = status match {
    case BodyFailed(error) => "crashed"
    case PostFailed(body, error) => "crashed in post"
    case PostInvalid(body) => "invalid post"
    case PostHeld(body) => "successful w/ valid post"
    case NoPost(body) => "successful"
  }
}

