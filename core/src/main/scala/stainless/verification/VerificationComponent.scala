/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package verification

import inox.utils.ASCIIHelpers._
import stainless.utils.JsonConvertions._
import stainless.verification.VCStatus.Invalid

import org.json4s.JsonDSL._
import org.json4s.JsonAST.{ JArray, JObject }

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

  override type Report = VerificationReport

  override val lowering = inox.ast.SymbolTransformer(new ast.TreeTransformer {
    val s: extraction.trees.type = extraction.trees
    val t: extraction.trees.type = extraction.trees
  })

  implicit val debugSection = DebugSectionVerification

  trait VerificationReport extends AbstractReport[VerificationReport] { self =>
    type Model = StainlessProgram#Model
    type Results = Map[VC[stainless.trees.type], VCResult[Model]]
    val results: Results

    lazy val vrs: Seq[(VC[stainless.trees.type], VCResult[Model])] =
      results.toSeq.sortBy { case (vc, _) => (vc.fd.name, vc.kind.toString) }

    lazy val totalConditions: Int = vrs.size
    lazy val totalTime = vrs.map(_._2.time.getOrElse(0l)).sum
    lazy val totalValid = vrs.count(_._2.isValid)
    lazy val totalValidFromCache = vrs.count(_._2.isValidFromCache)
    lazy val totalInvalid = vrs.count(_._2.isInvalid)
    lazy val totalUnknown = vrs.count(_._2.isInconclusive)

    override val name = VerificationComponent.this.name

    override def emitRowsAndStats: Option[(Seq[Row], ReportStats)] = if (totalConditions == 0) None else Some((
      vrs.map { case (vc, vr) =>
        Row(Seq(
          Cell(vc.fd),
          Cell(vc.kind.name),
          Cell(vc.getPos.fullString),
          Cell(vr.status),
          Cell(vr.solver.map(_.name).getOrElse("")),
          Cell(vr.time.map(t => f"${t / 1000d}%3.3f").getOrElse(""))
        ))
      },
      ReportStats(totalConditions, totalTime, totalValid, totalValidFromCache, totalInvalid, totalUnknown)
    ))

    // Group by function, overriding all VCResults by the ones in `other`.
    override def ~(other: VerificationReport): VerificationReport = {
      def buildMapping(subs: Results): Map[Identifier, Results] = subs groupBy { case (vc, _) => vc.fd }

      val prev = buildMapping(this.results)
      val next = buildMapping(other.results)

      val fused = (prev ++ next).values.fold(Map.empty)(_ ++ _)

      new VerificationReport { override val results = fused }
    }

    override def removeSubreports(ids: Seq[Identifier]) = new VerificationReport {
      override val results = self.results filterNot { case (vc, _) => ids contains vc.fd }
    }

    override def emitJson: JArray = {
      def status2Json(status: VCStatus[Model]): JObject = status match {
        case Invalid(cex) =>
          val info = cex.vars map { case (vd, e) => vd.id.name -> e.toString }
          ("status" -> status.name) ~ ("counterexample" -> info)

        case _ => "status" -> status.name
      }

      val report: JArray = for { (vc, vr) <- vrs } yield {
        ("fd" -> vc.fd.name) ~
        ("pos" -> vc.getPos.toJson) ~
        ("kind" -> vc.kind.name) ~
        status2Json(vr.status) ~
        ("time" -> vr.time)
      }

      report
    }
  }

  def check(funs: Seq[Identifier], p: StainlessProgram, ctx: inox.Context): Map[VC[p.trees.type], VCResult[p.Model]] = {
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

  def apply(funs: Seq[Identifier], p: StainlessProgram, ctx: inox.Context): VerificationReport = {
    val res = check(funs, p, ctx)

    new VerificationReport { override val results = res }
  }
}

