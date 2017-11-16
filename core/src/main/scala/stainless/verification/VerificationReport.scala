/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package verification

import inox.utils.ASCIIHelpers.{ Cell, Row }
import stainless.utils.JsonConvertions._

import io.circe._
import io.circe.syntax._
import io.circe.generic.semiauto._

import scala.util.{ Right, Left }

object VerificationReport {

  /**
   * Similar interface to [[VCStatus]], but with text only data and all
   * inconclusive status mapped to [[Inconclusive]].
   */
  sealed abstract class Status(val name: String) {
    def isValid = this == Status.Valid || isValidFromCache
    def isValidFromCache = this == Status.ValidFromCache
    def isInvalid = this.isInstanceOf[Status.Invalid]
    def isInconclusive = this.isInstanceOf[Status.Inconclusive]
  }

  object Status {
    type VariableName = String
    type Value = String

    case object Valid extends Status("valid")
    case object ValidFromCache extends Status("valid from cache")
    case class Inconclusive(reason: String) extends Status(reason)
    case class Invalid(counterexample: Map[VariableName, Value]) extends Status("invalid")

    def apply[Model <: StainlessProgram#Model](status: VCStatus[Model]): Status = status match {
      case VCStatus.Invalid(model) => Invalid(model.vars map { case (vd, e) => vd.id.name -> e.toString })
      case VCStatus.Valid => Valid
      case VCStatus.ValidFromCache => ValidFromCache
      case inconclusive => Inconclusive(inconclusive.name)
    }
  }

  implicit val statusDecoder: Decoder[Status] = deriveDecoder
  implicit val statusEncoder: Encoder[Status] = deriveEncoder

  case class Record(
    id: Identifier, pos: inox.utils.Position, time: Long,
    status: Status, solverName: Option[String], kind: String,
    derivedFrom: Identifier
  ) extends AbstractReportHelper.Record

  implicit val recordDecoder: Decoder[Record] = deriveDecoder
  implicit val recordEncoder: Encoder[Record] = deriveEncoder

  def parse(json: Json) = json.as[Seq[Record]] match {
    case Right(records) => new VerificationReport(records)
    case Left(error) => throw error
  }

}

class VerificationReport(val results: Seq[VerificationReport.Record])
  extends AbstractReport[VerificationReport] {
  import VerificationReport._

  lazy val totalConditions: Int = results.size
  lazy val totalTime = results.map(_.time).sum
  lazy val totalValid = results.count(_.status.isValid)
  lazy val totalValidFromCache = results.count(_.status.isValidFromCache)
  lazy val totalInvalid = results.count(_.status.isInvalid)
  lazy val totalUnknown = results.count(_.status.isInconclusive)

  override val name = VerificationComponent.name

  override lazy val annotatedRows = results map {
    case Record(id, pos, time, status, solverName, kind, _) =>
      val level = levelOf(status)
      val solver = solverName getOrElse ""
      val extra = Seq(kind, status.name, solver)

      RecordRow(id, pos, level, extra, time)
  }

  private def levelOf(status: Status) = {
    if (status.isValid) Level.Normal
    else if (status.isInconclusive) Level.Warning
    else Level.Error
  }

  override lazy val stats =
    ReportStats(totalConditions, totalTime, totalValid, totalValidFromCache, totalInvalid, totalUnknown)

  override def ~(other: VerificationReport) =
    new VerificationReport(AbstractReportHelper.merge(this.results, other.results))

  override def filter(ids: Set[Identifier]) =
    new VerificationReport(AbstractReportHelper.filter(results, ids))

  override def emitJson: Json = results.asJson

}

