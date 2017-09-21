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
    fid: Identifier, pos: inox.utils.Position, time: Long,
    status: Status, solverName: Option[String], kind: String,
    generation: Long = 0 // "age" of the record, usefull to determine which ones are "NEW".
  )

  implicit val recordDecoder: Decoder[Record] = deriveDecoder
  implicit val recordEncoder: Encoder[Record] = deriveEncoder

  def parse(json: Json) = json.as[(Seq[Record], Long)] match {
    case Right((records, lastGen)) => new VerificationReport(records, lastGen + 1)
    case Left(error) => throw error
  }

}

class VerificationReport(val results: Seq[VerificationReport.Record], lastGen: Long = 0)
  extends AbstractReport[VerificationReport] {
  import VerificationReport._

  lazy val totalConditions: Int = results.size
  lazy val totalTime = results.map(_.time).sum
  lazy val totalValid = results.count(_.status.isValid)
  lazy val totalValidFromCache = results.count(_.status.isValidFromCache)
  lazy val totalInvalid = results.count(_.status.isInvalid)
  lazy val totalUnknown = results.count(_.status.isInconclusive)

  override val name = VerificationComponent.name

  override def emitRowsAndStats: Option[(Seq[Row], ReportStats)] = if (totalConditions == 0) None else Some((
    results sortBy { _.fid } map { case Record(fid, pos, time, status, solverName, kind, gen) =>
      Row(Seq(
        Cell(if (gen == lastGen) "NEW" else ""),
        Cell(fid),
        Cell(kind),
        Cell(pos.fullString),
        Cell(status.name),
        Cell(solverName getOrElse ""),
        Cell(f"${time / 1000d}%3.3f")
      ))
    },
    ReportStats(totalConditions, totalTime, totalValid, totalValidFromCache, totalInvalid, totalUnknown)
  ))

  override def ~(other: VerificationReport): VerificationReport = {
    def buildMapping(subs: Seq[Record]): Map[Identifier, Seq[Record]] = subs groupBy { _.fid }

    val prev = buildMapping(this.results)
    val next0 = buildMapping(other.results)

    // Update the generation only if we are not simply adding things to the current (parallel) generation.
    val nextGen = if ((prev.keySet & next0.keySet).isEmpty) lastGen else lastGen + 1

    val next = next0 mapValues {
      records => records map { r => r.copy(generation = nextGen) }
    }

    val fused = (prev ++ next).values.fold(Seq.empty)(_ ++ _)

    new VerificationReport(fused, nextGen)
  }

  override def filter(ids: Set[Identifier]) =
    new VerificationReport(results filter { ids contains _.fid }, lastGen + 1)

  override def emitJson: Json = (results, lastGen).asJson

}

