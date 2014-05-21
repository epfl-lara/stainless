/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package verification

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._

import solvers._
import solvers.z3._
import solvers.combinators._

import scala.collection.mutable.{Set => MutableSet}

import _root_.smtlib.interpreters.Z3Interpreter

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

    val toVerify = program.definedFunctions.toList.sortWith((fd1, fd2) => fd1.getPos < fd2.getPos).filter(fdFilter)

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

  def checkVerificationConditions(vctx: VerificationContext, vcs: Map[FunDef, List[VerificationCondition]]) : VerificationReport = {
    import vctx.reporter
    import vctx.solverFactory
    import vctx.program

    val interruptManager = vctx.context.interruptManager

    for((funDef, vcs) <- vcs.toSeq.sortWith((a,b) => a._1.getPos < b._1.getPos); vcInfo <- vcs if !interruptManager.isInterrupted()) {
      val funDef = vcInfo.funDef
      val vc = vcInfo.condition

      // Check if vc targets abstract methods
      val targets = functionCallsOf(vc).map(_.tfd.fd)
      val callsAbstract = (vctx.program.callGraph.transitiveCallees(targets) ++ targets).exists(_.annotations("abstract"))

      reporter.info("Now considering '" + vcInfo.kind + "' VC for " + funDef.id + "...")
      reporter.debug("Verification condition (" + vcInfo.kind + ") for ==== " + funDef.id + " ====")
      reporter.debug(simplifyLets(vc).asString(vctx.context))

      val s = solverFactory.getNewSolver
      try {
        reporter.debug("Solving with: " + s.name)
        val t1 = System.nanoTime
        s.assertCnstr(Not(vc))

        val satResult = s.check
        val counterexample: Map[Identifier, Expr] = if (satResult == Some(true)) s.getModel else Map()
        val solverResult = satResult.map(!_)

        val t2 = System.nanoTime
        val dt = ((t2 - t1) / 1000000) / 1000.0

        solverResult match {
          case _ if interruptManager.isInterrupted() =>
            reporter.info("=== CANCELLED ===")
            vcInfo.time = Some(dt)
            false

          case None =>
            vcInfo.hasValue = true
            reporter.warning("==== UNKNOWN ====")
            vcInfo.time = Some(dt)
            false

          case Some(true) =>
            reporter.info("==== VALID ====")

            vcInfo.hasValue = true
            vcInfo.value = Some(true)
            vcInfo.solvedWith = Some(s)
            vcInfo.time = Some(dt)
            true

          case Some(false) =>
            reporter.error("Found counter-example : ")
            reporter.error(counterexample.toSeq.sortBy(_._1.name).map(p => p._1 + " -> " + p._2).mkString("\n"))
            reporter.error("==== INVALID ====")
            vcInfo.hasValue = true
            vcInfo.value = Some(false)
            vcInfo.solvedWith = Some(s)
            vcInfo.counterExample = Some(counterexample)
            vcInfo.time = Some(dt)
            true
        }
      } finally {
        s.free()
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
    val entrySolver = SolverFactory.getFromSettings(ctx, program)

    val mainSolver = timeout match {
      case Some(sec) =>
        new TimeoutSolverFactory(entrySolver, sec*1000L)
      case None =>
        entrySolver
    }

    val vctx = VerificationContext(ctx, program, mainSolver, reporter)

    reporter.debug("Running verification condition generation...")
    val vcs = generateVerificationConditions(vctx, filterFuns)
    checkVerificationConditions(vctx, vcs)
  }
}
