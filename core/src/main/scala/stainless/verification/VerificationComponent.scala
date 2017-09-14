/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package verification

import inox.utils.ASCIIHelpers._
import stainless.utils.JsonConvertions._
import stainless.verification.VCStatus.Invalid

import org.json4s.JsonDSL._
import org.json4s.JsonAST._

import scala.language.existentials

/**
 * Strict Arithmetic Mode:
 *
 * Add assertions for integer overflow checking and other unexpected behaviour (e.g. x << 65).
 */
object optStrictArithmetic extends inox.FlagOptionDef("strictarithmetic", false)

object VerificationComponent extends SimpleComponent {
  override val name = "verification"
  override val description = "Verification of function contracts"

  override val trees: stainless.trees.type = stainless.trees

  override type Analysis = VerificationAnalysis

  override val lowering = inox.ast.SymbolTransformer(new ast.TreeTransformer {
    val s: extraction.trees.type = extraction.trees
    val t: extraction.trees.type = extraction.trees
  })

  implicit val debugSection = DebugSectionVerification

  // TODO re-introduce program in Analysis
  trait VerificationAnalysis extends AbstractAnalysis {

    override val name = VerificationComponent.this.name

    override type Report = VerificationReport

    override def toReport = new VerificationReport(vrs map { case (vc, vr) =>
      val time = vr.time.getOrElse(0L) // TODO make time mandatory (?)
      val status = VCTextStatus(vr.status)
      val solverName = vr.solver map { _.name }
      TextRecord(vc.fd, vc.getPos, time, status, solverName, vc.kind.name)
    })

    type Model = StainlessProgram#Model
    type Results = Map[VC[stainless.trees.type], VCResult[Model]]
    val results: Results

    lazy val vrs: Seq[(VC[stainless.trees.type], VCResult[Model])] =
      results.toSeq.sortBy { case (vc, _) => (vc.fd.name, vc.kind.toString) }
  }

  /**
   * Similar interface to [[VCStatus]], but with text only data and all
   * inconclusive status mapped to [[Inconclusive]].
   */
  sealed abstract class VCTextStatus(val name: String) {
    def isValid = this == VCTextStatus.Valid || isValidFromCache
    def isValidFromCache = this == VCTextStatus.ValidFromCache
    def isInvalid = this.isInstanceOf[VCTextStatus.Invalid]
    def isInconclusive = this.isInstanceOf[VCTextStatus.Inconclusive]

    def toJson: JObject = this match {
      case VCTextStatus.Invalid(vars) => ("status" -> name) ~ ("counterexample" -> vars)
      case _ => "status" -> name
    }
  }

  object VCTextStatus {
    type VariableName = String
    type Value = String

    case object Valid extends VCTextStatus("valid")
    case object ValidFromCache extends VCTextStatus("valid from cache")
    case class Inconclusive(reason: String) extends VCTextStatus(reason)
    case class Invalid(counterexample: Map[VariableName, Value]) extends VCTextStatus("invalid")

    def apply[Model <: Program#Model](status: VCStatus[Model]): VCTextStatus = status match {
      case VCStatus.Invalid(model) => Invalid(model.vars map { case (vd, e) => vd.id.name -> e.toString })
      case VCStatus.Valid => Valid
      case VCStatus.ValidFromCache => ValidFromCache
      case inconclusive => Inconclusive(inconclusive.name)
    }
  }

  case class TextRecord(
    fid: Identifier, pos: inox.utils.Position, time: Long,
    status: VCTextStatus, solverName: Option[String], kind: String
  )

  // TODO move to its own file (and do the same for Termination)
  // TODO create generic interface to reduce work with TerminationReport
  class VerificationReport(val results: Seq[TextRecord]) extends AbstractReport[VerificationReport] {

    lazy val totalConditions: Int = results.size
    lazy val totalTime = results.map(_.time).sum
    lazy val totalValid = results.count(_.status.isValid)
    lazy val totalValidFromCache = results.count(_.status.isValidFromCache)
    lazy val totalInvalid = results.count(_.status.isInvalid)
    lazy val totalUnknown = results.count(_.status.isInconclusive)

    override val name = VerificationComponent.this.name

    override def emitRowsAndStats: Option[(Seq[Row], ReportStats)] = if (totalConditions == 0) None else Some((
      results map { case TextRecord(fid, pos, time, status, solverName, kind) =>
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
      def buildMapping(subs: Seq[TextRecord]): Map[Identifier, Seq[TextRecord]] = subs groupBy { _.fid }

      val prev = buildMapping(this.results)
      val next = buildMapping(other.results)

      val fused = (prev ++ next).values.fold(Seq.empty)(_ ++ _)

      new VerificationReport(fused)
    }

    override def invalidate(ids: Seq[Identifier]) =
      new VerificationReport(results filterNot { ids contains _.fid })

    override def emitJson: JArray =
      for { TextRecord(fid, pos, time, status, solverName, kind) <- results } yield {
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

  object VerificationReport {
    def parse(json: JValue) = ??? // TODO
  }

  private def check(funs: Seq[Identifier], p: StainlessProgram, ctx: inox.Context): Map[VC[p.trees.type], VCResult[p.Model]] = {
    val injector = AssertionInjector(p, ctx)
    val encoder = inox.ast.ProgramEncoder(p)(injector)

    import ctx._
    import encoder.targetProgram._
    import encoder.targetProgram.trees._
    import encoder.targetProgram.symbols._

    val toVerify = funs.sortBy(getFunction(_).getPos)
    ctx.reporter.debug(s"Generating VCs for those functions: ${toVerify map { _.uniqueName } mkString ", "}")

    for (id <- toVerify) {
      if (getFunction(id).flags contains "library") {
        val fullName = id.fullName
        reporter.warning(s"Forcing verification of $fullName which was assumed verified")
      }
    }

    val vcs = VerificationGenerator.gen(encoder.targetProgram, ctx)(toVerify)

    VerificationChecker.verify(encoder.targetProgram, ctx)(vcs).mapValues {
      case VCResult(VCStatus.Invalid(model), s, t) =>
        VCResult(VCStatus.Invalid(model.encode(encoder.reverse)), s, t)
      case res => res.asInstanceOf[VCResult[p.Model]]
    }
  }

  override def apply(funs: Seq[Identifier], p: StainlessProgram, ctx: inox.Context): VerificationAnalysis = {
    val res = check(funs, p, ctx)

    new VerificationAnalysis { override val results = res }
  }
}

