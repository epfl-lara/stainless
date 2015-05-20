/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package verification

import purescala.Definitions._
import purescala.ExprOps._

import scala.concurrent.duration._

import solvers._
import solvers.smtlib.SMTLIBCVC4QuantifiedSolver

object AnalysisPhase extends LeonPhase[Program,VerificationReport] {
  val name = "Analysis"
  val description = "Leon Verification"

  implicit val debugSection = utils.DebugSectionVerification

  def run(ctx: LeonContext)(program: Program): VerificationReport = {
    val filterFuns: Option[Seq[String]] = ctx.findOption(SharedOptions.optFunctions)
    val timeout:    Option[Long]        = ctx.findOption(SharedOptions.optTimeout)

    val reporter = ctx.reporter

    // Solvers selection and validation
    val baseSolverF = SolverFactory.getFromSettings(ctx, program)

    val solverF = timeout match {
      case Some(sec) =>
        baseSolverF.withTimeout(sec.seconds)
      case None =>
        baseSolverF
    }

    val vctx = VerificationContext(ctx, program, solverF, reporter)

    reporter.debug("Generating Verification Conditions...")

    try { 
      val vcs = generateVCs(vctx, filterFuns, forceGrouped = baseSolverF.getNewSolver.isInstanceOf[SMTLIBCVC4QuantifiedSolver])

      reporter.debug("Checking Verification Conditions...")

      checkVCs(vctx, vcs)
    } finally {
      solverF.shutdown()
    }
  }

  def generateVCs(vctx: VerificationContext, filterFuns: Option[Seq[String]], forceGrouped: Boolean = false): Seq[VC] = {

    import vctx.reporter
    import vctx.program

    val defaultTactic   = new DefaultTactic(vctx)
    val inductionTactic = new InductionTactic(vctx)
    val groupedTactic   = new GroupedTactic(vctx)

    def excludeByDefault(fd: FunDef): Boolean = fd.annotations contains "library"

    val fdFilter = {
      import OptionsHelpers._

      filterInclusive(filterFuns.map(fdMatcher), Some(excludeByDefault _))
    }

    val toVerify = program.definedFunctions.filter(fdFilter).sortWith((fd1, fd2) => fd1.getPos < fd2.getPos)

    val vcs = for(funDef <- toVerify) yield {
      if (excludeByDefault(funDef)) {
        reporter.warning("Forcing verification of "+funDef.id.name+" which was assumed verified")
      }

      val tactic: Tactic =
        if (forceGrouped) {
          groupedTactic
        } else if(funDef.annotations.contains("induct")) {
          inductionTactic
        } else {
          defaultTactic
        }

      if(funDef.body.isDefined) {
        tactic.generateVCs(funDef)
      } else {
        Nil
      }
    }

    vcs.flatten
  }

  def checkVCs(
    vctx: VerificationContext,
    vcs: Seq[VC],
    checkInParallel: Boolean = false,
    stopAfter: Option[(VC, VCResult) => Boolean] = None
  ): VerificationReport = {
    val interruptManager = vctx.context.interruptManager

    var stop = false

    val initMap: Map[VC, Option[VCResult]] = vcs.map(v => v -> None).toMap

    val results = if (checkInParallel) {
      for (vc <- vcs.par if !stop) yield {
        val r = checkVC(vctx, vc)
        if (interruptManager.isInterrupted) interruptManager.recoverInterrupt()
        stop = stopAfter.exists(_(vc, r))
        vc -> Some(r)
      }
    } else {
      for (vc <- vcs.toSeq.sortWith((a,b) => a.fd.getPos < b.fd.getPos) if !interruptManager.isInterrupted && !stop) yield {
        val r = checkVC(vctx, vc)
        if (interruptManager.isInterrupted) interruptManager.recoverInterrupt()
        stop = stopAfter.exists(_(vc, r))
        vc -> Some(r)
      }
    }

    VerificationReport(initMap ++ results)
  }

  def checkVC(vctx: VerificationContext, vc: VC): VCResult = {
    import vctx.reporter
    import vctx.solverFactory

    val interruptManager = vctx.context.interruptManager

    val vcCond = vc.condition

    val s = solverFactory.getNewSolver()

    try {
      reporter.synchronized {
        reporter.info(s" - Now considering '${vc.kind}' VC for ${vc.fd.id} @${vc.getPos}...")
        reporter.debug(simplifyLets(vcCond).asString(vctx.context))
        reporter.debug("Solving with: " + s.name)
      }

      val tStart = System.currentTimeMillis

      s.assertVC(vc)

      val satResult = s.check

      val dt = System.currentTimeMillis - tStart

      val res = satResult match {
        case _ if interruptManager.isInterrupted =>
          VCResult(VCStatus.Cancelled, Some(s), Some(dt))

        case None =>
          VCResult(VCStatus.Unknown, Some(s), Some(dt))

        case Some(false) =>
          VCResult(VCStatus.Valid, Some(s), Some(dt))

        case Some(true) =>
          VCResult(VCStatus.Invalid(s.getModel), Some(s), Some(dt))
      }

      reporter.synchronized {
        res.report(vctx)
      }

      res

    } finally {
      s.free()
    }
  }
}
