/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package verification

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._

import solvers._

object AnalysisPhase extends LeonPhase[Program,VerificationReport] {
  val name = "Analysis"
  val description = "Leon Verification"

  implicit val debugSection = utils.DebugSectionVerification

  override val definedOptions : Set[LeonOptionDef] = Set(
    LeonValueOptionDef("functions", "--functions=f1:f2", "Limit verification to f1,f2,..."),
    LeonValueOptionDef("timeout",   "--timeout=T",       "Timeout after T seconds when trying to prove a verification condition.")
  )

  def generateVerificationConditions(vctx: VerificationContext, filterFuns: Option[Seq[String]]): Map[FunDef, List[VerificationCondition]] = {

    import vctx.reporter
    import vctx.program

    val defaultTactic = new DefaultTactic(vctx)
    val inductionTactic = new InductionTactic(vctx)

    var allVCs = Map[FunDef, List[VerificationCondition]]()

    def excludeByDefault(fd: FunDef): Boolean = {
      (fd.annotations contains "verified") || (fd.annotations contains "library")
    }

    val fdFilter = {
      import OptionsHelpers._

      filterInclusive(filterFuns.map(fdMatcher), Some(excludeByDefault _))
    }

    val toVerify = program.definedFunctions.filter(fdFilter).sortWith((fd1, fd2) => fd1.getPos < fd2.getPos)

    for(funDef <- toVerify) {
      if (excludeByDefault(funDef)) {
        reporter.warning("Forcing verification of "+funDef.id.name+" which was assumed verified")
      }

      val tactic: Tactic =
        if(funDef.annotations.contains("induct")) {
          inductionTactic
        } else {
          defaultTactic
        }

      if(funDef.body.isDefined) {
        val funVCs = tactic.generateVCs(funDef)

        allVCs += funDef -> funVCs.toList
      }
    }

    allVCs
  }

  def checkVerificationConditions(
      vctx: VerificationContext, 
      vcs: Map[FunDef, List[VerificationCondition]], 
      checkInParallel: Boolean = false,
      stopAfter : VerificationCondition => Boolean = { _ => false }
  ) : VerificationReport = {
    import vctx.reporter
    import vctx.solverFactory
    
    val interruptManager = vctx.context.interruptManager

    def checkVC(vcInfo : VerificationCondition) = {
      val funDef = vcInfo.funDef
      val vc = vcInfo.condition

      // Check if vc targets abstract methods
      val targets = functionCallsOf(vc).map(_.tfd.fd)

      val s = solverFactory.getNewSolver
      try {
        
        reporter.synchronized {
          reporter.info(s" - Now considering '${vcInfo.kind}' VC for ${funDef.id} @${vcInfo.getPos}...")
          reporter.debug("Verification condition (" + vcInfo.kind + ") for ==== " + funDef.id + " ====")
          reporter.debug(simplifyLets(vc).asString(vctx.context))
          reporter.debug("Solving with: " + s.name)
        }
        
        val t1 = System.nanoTime
        s.assertCnstr(Not(vc))

        val satResult = s.check
        val counterexample: Map[Identifier, Expr] = if (satResult == Some(true)) s.getModel else Map()
        val solverResult = satResult.map(!_)

        val t2 = System.nanoTime
        val dt = ((t2 - t1) / 1000000) / 1000.0
        
        reporter.synchronized {
          def title(s : String) = s"   => $s"
          solverResult match {
            case _ if interruptManager.isInterrupted =>
              reporter.warning(title("CANCELLED"))
              vcInfo.time = Some(dt)
              false
  
            case None =>
              vcInfo.hasValue = true
              reporter.warning(title("UNKNOWN"))
              vcInfo.time = Some(dt)
              false
  
            case Some(true) =>
              reporter.info(title("VALID"))
  
              vcInfo.hasValue = true
              vcInfo.value = Some(true)
              vcInfo.solvedWith = Some(s)
              vcInfo.time = Some(dt)
              true
  
            case Some(false) =>
              reporter.error(title("INVALID"))
              reporter.error("Found counter-example : ")
              reporter.error(counterexample.toSeq.sortBy(_._1.name).map(p => p._1 + " -> " + p._2).mkString("\n"))
              vcInfo.hasValue = true
              vcInfo.value = Some(false)
              vcInfo.solvedWith = Some(s)
              vcInfo.counterExample = Some(counterexample)
              vcInfo.time = Some(dt)
              true
          }
        }
      } finally {
        s.free()
      }
    }
    
    var stop = false
    
    if (checkInParallel) {
      val allVCsPar = (for {(_, vcs) <- vcs.toSeq; vcInfo <- vcs} yield vcInfo).par
      for (vc <- allVCsPar if !stop) {
        checkVC(vc)
        if (interruptManager.isInterrupted) interruptManager.recoverInterrupt()
        stop = stopAfter(vc)
      }
    } else {
      for {
        (funDef, vcs) <- vcs.toSeq.sortWith((a,b) => a._1.getPos < b._1.getPos)
        vc <- vcs if !interruptManager.isInterrupted && !stop
      } {
        checkVC(vc)
        if (interruptManager.isInterrupted) interruptManager.recoverInterrupt()
        stop = stopAfter(vc)
      }
    }
    
    val report = new VerificationReport(vcs)
    report
  }

  def run(ctx: LeonContext)(program: Program) : VerificationReport = {
    var filterFuns: Option[Seq[String]] = None
    var timeout: Option[Int]             = None

    val reporter = ctx.reporter

    for(opt <- ctx.options) opt match {
      case LeonValueOption("functions", ListValue(fs)) =>
        filterFuns = Some(fs)


      case v @ LeonValueOption("timeout", _) =>
        timeout = v.asInt(ctx)

      case _ =>
    }

    // Solvers selection and validation
    val entrySolverFactory = SolverFactory.getFromSettings(ctx, program)

    val mainSolverFactory = timeout match {
      case Some(sec) =>
        new TimeoutSolverFactory(entrySolverFactory, sec*1000L)
      case None =>
        entrySolverFactory
    }

    val vctx = VerificationContext(ctx, program, mainSolverFactory, reporter)

    reporter.debug("Running verification condition generation...")
    val vcs = generateVerificationConditions(vctx, filterFuns)
    checkVerificationConditions(vctx, vcs)
  }
}
