/* Copyright 2009-2019 EPFL, Lausanne */

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
    case object Valid extends Status("valid")
    case object ValidFromCache extends Status("valid from cache")
    case class Inconclusive(reason: String) extends Status(reason)
    case class Invalid(reason: String) extends Status("invalid")

    def apply[Model <: StainlessProgram#Model](program: inox.Program)
                                              (status: VCStatus[program.Model])
                                              (implicit opts: program.trees.PrinterOptions): Status = status match {
      case VCStatus.Invalid(VCStatus.CounterExample(model)) => Invalid("counter-example: " + model.asString)
      case VCStatus.Invalid(VCStatus.Unsatisfiable) => Invalid("unsatisfiable")
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

  def parse(json: Json) = json.as[(Seq[Record], Set[Identifier])] match {
    case Right((records, sources)) => new VerificationReport(records, sources)
    case Left(error) => throw error
  }

}

class VerificationReport(val results: Seq[VerificationReport.Record], val sources: Set[Identifier])
  extends BuildableAbstractReport[VerificationReport.Record, VerificationReport] {
  import VerificationReport._

  override val encoder = recordEncoder

  override def build(results: Seq[Record], sources: Set[Identifier]) =
    new VerificationReport(results, sources)

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

}

