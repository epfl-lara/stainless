/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package verification

import purescala.Definitions._
import purescala.ExprOps._

import scala.concurrent.duration._

import solvers._

object VerificationPhase extends SimpleLeonPhase[Program,VerificationReport] {
  val name = "Verification"
  val description = "Verification of function contracts"

  val optParallelVCs = LeonFlagOptionDef("parallel", "Check verification conditions in parallel", default = false)  
  
  override val definedOptions: Set[LeonOptionDef[Any]] = Set(optParallelVCs)

  implicit val debugSection = utils.DebugSectionVerification
  
  /** Solvers selection and validation */
  def getSolverFactory(ctx: LeonContext, program: Program): SolverFactory[Solver] = {
    val timeout:    Option[Long]        = ctx.findOption(GlobalOptions.optTimeout)
    val baseSolverF = SolverFactory.getFromSettings(ctx, program)

    val solverF = timeout match {
      case Some(sec) =>
        baseSolverF.withTimeout(sec.seconds)
      case None =>
        baseSolverF
    }
    solverF
  }

  def apply(ctx: LeonContext, program: Program): VerificationReport = {
    val filterFuns: Option[Seq[String]] = ctx.findOption(GlobalOptions.optFunctions)
    
    val reporter = ctx.reporter

    val solverF = getSolverFactory(ctx, program)

    val vctx = new VerificationContext(ctx, program, solverF)

    reporter.debug("Generating Verification Conditions...")

    def excludeByDefault(fd: FunDef): Boolean = fd.annotations contains "library"

    val fdFilter = {
      import OptionsHelpers._

      filterInclusive(filterFuns.map(fdMatcher(program)), Some(excludeByDefault _))
    }

    val toVerify = program.definedFunctions.filter(fdFilter).sortWith((fd1, fd2) => fd1.getPos < fd2.getPos)

    for(funDef <- toVerify) {
      if (excludeByDefault(funDef)) {
        reporter.warning("Forcing verification of " + funDef.qualifiedName(program) + " which was assumed verified")
      }
    }

    try {
      val vcs = generateVCs(vctx, toVerify)

      reporter.debug("Checking Verification Conditions...")

      checkVCs(vctx, vcs)
    } finally {
      solverF.shutdown()
    }
  }

  def generateVCs(vctx: VerificationContext, toVerify: Seq[FunDef]): Seq[VC] = {
    val defaultTactic   = new DefaultTactic(vctx)
    val inductionTactic = new InductionTactic(vctx)
    val trInductTactic = new TraceInductionTactic(vctx)

    val vcs = for(funDef <- toVerify) yield {
      val tactic: Tactic =
        if (funDef.annotations.contains("induct")) {
          inductionTactic
        } else if(funDef.annotations.contains("traceInduct")){
          trInductTactic
        }else {          
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
    stopWhen: VCResult => Boolean = _ => false
  ): VerificationReport = {
    val interruptManager = vctx.interruptManager

    var stop = false

    val initMap: Map[VC, Option[VCResult]] = vcs.map(v => v -> None).toMap

    val results = if (vctx.checkInParallel) {
      for (vc <- vcs.par if !stop) yield {
        val r = checkVC(vctx, vc)
        if (interruptManager.isInterrupted) interruptManager.recoverInterrupt()
        stop = stopWhen(r)
        vc -> Some(r)
      }
    } else {
      for (vc <- vcs.toSeq.sortWith((a,b) => a.fd.getPos < b.fd.getPos) if !interruptManager.isInterrupted && !stop) yield {
        val r = checkVC(vctx, vc)
        if (interruptManager.isInterrupted) interruptManager.recoverInterrupt()
        stop = stopWhen(r)
        vc -> Some(r)
      }
    }

    VerificationReport(vctx.program, initMap ++ results)
  }

  def checkVC(_vctx: VerificationContext, vc: VC): VCResult = {
    val vcCond = vc.condition

    val (finalSolverFactory: SolverFactory[_], vctx: VerificationContext) =  vc.fd.extAnnotations.get("options") match {
      case Some(seq) => // We rebuild the solverfactory.
        val newCtx = ((_vctx: LeonContext) /: seq) {
          case (ctx, Some(moreCommands: String)) =>
            ctx ++ leon.Main.parseOptions(leon.Main.splitOptions(moreCommands), true)
          case (ctx, Some((optionName: String, value: String))) =>
            ctx ++ Seq(leon.Main.parseOption("--" + optionName + "=" + value, true)).flatten
          case (ctx, _) => ctx
        }
        val solverF = getSolverFactory(newCtx, _vctx.program)
        val vctx = new VerificationContext(newCtx, _vctx.program, solverF)
        (solverF, vctx)
      case None => 
        (_vctx.solverFactory, _vctx)
    }
    import vctx.reporter
    import vctx.solverFactory
    val interruptManager = vctx.interruptManager
    
    val s = finalSolverFactory.getNewSolver

    try {
      reporter.synchronized {
        reporter.info(s" - Now considering '${vc.kind}' VC for ${vc.fd.id} @${vc.getPos}...")
        reporter.debug(simplifyLets(vcCond).asString(vctx))
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
          val status = s match {
            case ts: TimeoutSolver =>
              ts.optTimeout match {
                case Some(t) if t < dt =>
                  VCStatus.Timeout
                case _ =>
                  VCStatus.Unknown
              }
            case _ =>
              VCStatus.Unknown
          }
          VCResult(status, Some(s), Some(dt))

        case Some(false) =>
          VCResult(VCStatus.Valid, s.getResultSolver, Some(dt))

        case Some(true) =>
          VCResult(VCStatus.Invalid(s.getModel), s.getResultSolver, Some(dt))
      }

      reporter.synchronized {
        if (vctx.checkInParallel) {
          reporter.info(s" - Result for '${vc.kind}' VC for ${vc.fd.id} @${vc.getPos}:")
        }
        res.report(vctx)
      }

      res

    } finally {
      s.free()
    }
  }
}
