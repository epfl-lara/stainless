/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package verification

import inox.utils.ASCIIHelpers._
import stainless.utils.JsonConvertions._

import org.json4s.JsonDSL._
import org.json4s.JsonAST._

object VerificationReport {
  def parse(json: JValue) = ??? // TODO

  /**
   * Similar interface to [[VCStatus]], but with text only data and all
   * inconclusive status mapped to [[Inconclusive]].
   */
  sealed abstract class Status(val name: String) {
    def isValid = this == Status.Valid || isValidFromCache
    def isValidFromCache = this == Status.ValidFromCache
    def isInvalid = this.isInstanceOf[Status.Invalid]
    def isInconclusive = this.isInstanceOf[Status.Inconclusive]

    def toJson: JObject = this match {
      case Status.Invalid(vars) => ("status" -> name) ~ ("counterexample" -> vars)
      case _ => "status" -> name
    }
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

  case class Record(
    fid: Identifier, pos: inox.utils.Position, time: Long,
    status: Status, solverName: Option[String], kind: String
  )

}

// TODO create generic interface to reduce work with TerminationReport
class VerificationReport(val results: Seq[VerificationReport.Record]) extends AbstractReport[VerificationReport] {
  import VerificationReport._

  lazy val totalConditions: Int = results.size
  lazy val totalTime = results.map(_.time).sum
  lazy val totalValid = results.count(_.status.isValid)
  lazy val totalValidFromCache = results.count(_.status.isValidFromCache)
  lazy val totalInvalid = results.count(_.status.isInvalid)
  lazy val totalUnknown = results.count(_.status.isInconclusive)

  override val name = VerificationComponent.name

  override def emitRowsAndStats: Option[(Seq[Row], ReportStats)] = if (totalConditions == 0) None else Some((
    results map { case Record(fid, pos, time, status, solverName, kind) =>
      Row(Seq(
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
    val next = buildMapping(other.results)

    val fused = (prev ++ next).values.fold(Seq.empty)(_ ++ _)

    new VerificationReport(fused)
  }

  override def invalidate(ids: Seq[Identifier]) =
    new VerificationReport(results filterNot { ids contains _.fid })

  override def emitJson: JArray =
    for { Record(fid, pos, time, status, solverName, kind) <- results } yield {
      val solver: JValue = solverName match {
        case Some(name) => JString(name)
        case None => JNull
      }

      ("fd" -> fid.name) ~
      ("_fd" -> fid.toJson) ~
      ("pos" -> pos.toJson) ~
      ("time" -> time)
      status.toJson ~
      ("solver" -> solver) ~
      ("kind" -> kind)
    }
}

