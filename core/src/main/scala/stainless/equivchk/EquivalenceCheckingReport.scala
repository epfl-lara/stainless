package stainless
package equivchk

import io.circe._
import io.circe.generic.semiauto._
import io.circe.syntax._
import stainless.extraction._
import stainless.extraction.xlang.{trees => xt}
import stainless.termination.MeasureInference
import stainless.utils.JsonConvertions.given
import stainless.utils.{CheckFilter, JsonUtils}
import stainless.verification.VerificationReport.{Status => VerificationStatus}
import stainless.verification._

object EquivalenceCheckingReport {

  enum Status {
    case Verification(status: VerificationStatus)
    case Equivalence(status: EquivalenceStatus)

    def isValid: Boolean = this match {
      case Verification(status) => status.isValid
      case Equivalence(EquivalenceStatus.Valid(_, _, _)) => true
      case _ => false
    }

    def isValidFromCache: Boolean = this match {
      case Verification(status) => status.isValidFromCache
      case Equivalence(EquivalenceStatus.Valid(_, fromCache, _)) => fromCache
      case _ => false
    }

    def isTrivial: Boolean = this match {
      case Verification(status) => status.isTrivial
      case Equivalence(EquivalenceStatus.Valid(_, _, trivial)) => trivial
      case _ => false
    }

    def isInvalid: Boolean = this match {
      case Verification(status) => status.isInvalid
      case Equivalence(EquivalenceStatus.Erroneous | EquivalenceStatus.Wrong) => true
      case _ => false
    }

    def isInconclusive: Boolean = this match {
      case Verification(status) => status.isInconclusive
      case Equivalence(EquivalenceStatus.Unknown) => true
      case _ => false
    }
  }

  enum EquivalenceStatus {
    case Valid(model: Identifier, fromCache: Boolean, trivial: Boolean)
    case Erroneous
    case Wrong
    case Unknown
  }

  case class Record(id: Identifier, pos: inox.utils.Position, time: Long,
                    status: Status, solverName: Option[String], kind: String,
                    derivedFrom: Identifier) extends AbstractReportHelper.Record

  given equivStatusDecoder: Decoder[EquivalenceStatus] = deriveDecoder
  given equivStatusEncoder: Encoder[EquivalenceStatus] = deriveEncoder

  given statusDecoder: Decoder[Status] = deriveDecoder
  given statusEncoder: Encoder[Status] = deriveEncoder

  given recordDecoder: Decoder[Record] = deriveDecoder
  given recordEncoder: Encoder[Record] = deriveEncoder
}

class EquivalenceCheckingReport(override val results: Seq[EquivalenceCheckingReport.Record],
                                override val sources: Set[Identifier],
                                override val extractionSummary: ExtractionSummary) extends BuildableAbstractReport[EquivalenceCheckingReport.Record, EquivalenceCheckingReport] {
  import EquivalenceCheckingReport.{_, given}
  override protected val encoder: Encoder[Record] = recordEncoder

  override protected def build(results: Seq[Record], sources: Set[Identifier]): EquivalenceCheckingReport =
    new EquivalenceCheckingReport(results, sources, ExtractionSummary.NoSummary)

  override val name: String = EquivalenceCheckingComponent.name

  override lazy val annotatedRows: Seq[RecordRow] = results map {
    case Record(id, pos, time, status, solverName, kind, _) =>
      val statusName = status match {
        case Status.Verification(stat) => stat.name
        case Status.Equivalence(EquivalenceStatus.Valid(model, _, _)) => CheckFilter.fixedFullName(model)
        case Status.Equivalence(EquivalenceStatus.Wrong) => "signature mismatch"
        case Status.Equivalence(EquivalenceStatus.Erroneous) => "erroneous"
        case Status.Equivalence(EquivalenceStatus.Unknown) => "unknown"
      }
      val level = levelOf(status)
      val solver = solverName getOrElse ""
      val extra = Seq(kind, statusName, solver)
      RecordRow(id, pos, level, extra, time)
  }
  lazy val totalConditions: Int = results.size
  lazy val totalTime: Long = results.map(_.time).sum
  lazy val totalValid: Int = results.count(_.status.isValid)
  lazy val totalValidFromCache: Int = results.count(_.status.isValidFromCache)
  lazy val totalTrivial: Int = results.count(_.status.isTrivial)
  lazy val totalInvalid: Int = results.count(_.status.isInvalid)
  lazy val totalUnknown: Int = results.count(_.status.isInconclusive)

  private def levelOf(status: Status) = {
    if (status.isValid) Level.Normal
    else if (status.isInconclusive) Level.Warning
    else Level.Error
  }

  override lazy val stats: ReportStats =
    ReportStats(totalConditions, totalTime, totalValid, totalValidFromCache, totalTrivial, totalInvalid, totalUnknown)
}
