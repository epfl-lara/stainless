/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package verification

import inox.utils.ASCIIHelpers._
import stainless.utils.JsonConvertions._
import stainless.verification.VCStatus.Invalid

import org.json4s.JsonDSL._
import org.json4s.JsonAST.{ JArray, JObject }

import scala.language.existentials

object VerificationComponent extends SimpleComponent {
  val name = "verification"
  val description = "Verification of function contracts"

  /**
   * Strict Arithmetic Mode:
   *
   * Add assertions for integer overflow checking and other unexpected behaviour (e.g. x << 65).
   */
  val optStrictArithmetic = inox.FlagOptionDef("strictarithmetic", false)

  val trees: stainless.trees.type = stainless.trees

  type Report = VerificationReport

  val lowering = inox.ast.SymbolTransformer(new ast.TreeTransformer {
    val s: extraction.trees.type = extraction.trees
    val t: extraction.trees.type = extraction.trees
  })

  implicit val debugSection = DebugSectionVerification

  trait VerificationReport extends AbstractReport { self =>
    val program: Program { val trees: stainless.trees.type }
    val results: Map[VC[program.trees.type], VCResult[program.Model]]

    import program.{ Model }

    lazy val vrs = results.toSeq.sortBy { case (vc, _) => (vc.fd.name, vc.kind.toString) }

    lazy val totalConditions = vrs.size
    lazy val totalTime = vrs.map(_._2.time.getOrElse(0l)).sum
    lazy val totalValid = vrs.count(_._2.isValid)
    lazy val totalInvalid = vrs.count(_._2.isInvalid)
    lazy val totalUnknown = vrs.count(_._2.isInconclusive)

    override val name = VerificationComponent.this.name

    override def emitRowsAndStats: Option[(Seq[Row], ReportStats)] = if (totalConditions == 0) None else Some(
      vrs.map { case (vc, vr) =>
        Row(Seq(
          Cell(vc.fd),
          Cell(vc.kind.name),
          Cell(vc.getPos),
          Cell(vr.status),
          Cell(vr.solver.map(_.name).getOrElse("")),
          Cell(vr.time.map(t => f"${t/1000d}%3.3f").getOrElse(""))
        ))
      }, ReportStats(totalConditions, totalTime, totalValid, totalInvalid, totalUnknown)
    )

    override def emitJson: JArray = {
      def status2Json(status: VCStatus[Model]): JObject = status match {
        case Invalid(cex) =>
          val info = cex.vars map { case (vd, e) => (vd.id.name -> e.toString) }
          ("status" -> status.name) ~ ("counterexample" -> info)

        case status => ("status" -> status.name)
      }

      val report: JArray = for { (vc, vr) <- vrs } yield {
        ("fd" -> vc.fd.name) ~
        ("pos" -> vc.getPos.toJson) ~
        ("kind" -> vc.kind.name) ~
        status2Json(vr.status)
      }

      report
    }
  }

  def check(funs: Seq[Identifier], p: StainlessProgram): Map[VC[p.trees.type], VCResult[p.Model]] = {
    val injector = AssertionInjector(p)
    val encoder = inox.ast.ProgramEncoder(p)(injector)

    import encoder.targetProgram._
    import encoder.targetProgram.trees._
    import encoder.targetProgram.symbols._

    val toVerify = funs.sortBy(getFunction(_).getPos)

    for (id <- toVerify) {
      if (getFunction(id).flags contains "library") {
        val fullName = id.fullName
        ctx.reporter.warning(s"Forcing verification of $fullName which was assumed verified")
      }
    }

    VerificationChecker.verify(encoder.targetProgram)(funs).mapValues {
      case VCResult(VCStatus.Invalid(model), s, t) =>
        VCResult(VCStatus.Invalid(model.encode(encoder.reverse)), s, t)
      case res => res.asInstanceOf[VCResult[p.Model]]
    }
  }

  def apply(funs: Seq[Identifier], p: StainlessProgram): VerificationReport = {
    val res = check(funs, p)

    new VerificationReport {
      val program: p.type = p
      val results = res
    }
  }
}
