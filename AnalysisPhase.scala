/* Copyright 2009-2013 EPFL, Lausanne */

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

object AnalysisPhase extends LeonPhase[Program,VerificationReport] {
  val name = "Analysis"
  val description = "Leon Verification"

  implicit val debugSection = utils.DebugSectionVerification

  override val definedOptions : Set[LeonOptionDef] = Set(
    LeonValueOptionDef("functions", "--functions=f1:f2", "Limit verification to f1,f2,..."),
    LeonValueOptionDef("timeout",   "--timeout=T",       "Timeout after T seconds when trying to prove a verification condition.")
  )

  def generateVerificationConditions(reporter: Reporter, program: Program, functionsToAnalyse: Set[String]): Map[FunDef, List[VerificationCondition]] = {
    val defaultTactic = new DefaultTactic(reporter)
    defaultTactic.setProgram(program)
    val inductionTactic = new InductionTactic(reporter)
    inductionTactic.setProgram(program)

    var allVCs = Map[FunDef, List[VerificationCondition]]()

    for(funDef <- program.definedFunctions.toList.sortWith((fd1, fd2) => fd1.getPos < fd2.getPos) if (functionsToAnalyse.isEmpty || functionsToAnalyse.contains(funDef.id.name))) {

      val tactic: Tactic =
        if(funDef.annotations.contains("induct")) {
          inductionTactic
        } else {
          defaultTactic
        }

      if(funDef.body.isDefined) {
        val funVCs = tactic.generatePreconditions(funDef) ++
                     tactic.generatePatternMatchingExhaustivenessChecks(funDef) ++
                     tactic.generatePostconditions(funDef) ++
                     tactic.generateMiscCorrectnessConditions(funDef) ++
                     tactic.generateArrayAccessChecks(funDef)

        allVCs += funDef -> funVCs.toList
      }
    }

    val notFound = functionsToAnalyse -- allVCs.keys.map(_.id.name)
    notFound.foreach(fn => reporter.error("Did not find function \"" + fn + "\" though it was marked for analysis."))

    allVCs
  }

  def checkVerificationConditions(vctx: VerificationContext, vcs: Map[FunDef, List[VerificationCondition]]) : VerificationReport = {
    val reporter = vctx.reporter
    val solvers  = vctx.solvers

    val interruptManager = vctx.context.interruptManager

    for((funDef, vcs) <- vcs.toSeq.sortWith((a,b) => a._1.getPos < b._1.getPos); vcInfo <- vcs if !interruptManager.isInterrupted()) {
      val funDef = vcInfo.funDef
      val vc = vcInfo.condition

      reporter.info("Now considering '" + vcInfo.kind + "' VC for " + funDef.id + "...")
      reporter.debug("Verification condition (" + vcInfo.kind + ") for ==== " + funDef.id + " ====")
      reporter.debug(simplifyLets(vc).asString(vctx.context))

      // try all solvers until one returns a meaningful answer
      solvers.find(sf => {
        val s = sf.getNewSolver
        try {
          reporter.debug("Trying with solver: " + s.name)
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
        }}) match {
          case None => {
            vcInfo.hasValue = true
            reporter.warning("==== UNKNOWN ====")
          }
          case _ =>
        }
    }

    val report = new VerificationReport(vcs)
    report
  }

  def run(ctx: LeonContext)(program: Program) : VerificationReport = {
    var functionsToAnalyse   = Set[String]()
    var timeout: Option[Int] = None

    for(opt <- ctx.options) opt match {
      case LeonValueOption("functions", ListValue(fs)) =>
        functionsToAnalyse = Set() ++ fs

      case v @ LeonValueOption("timeout", _) =>
        timeout = v.asInt(ctx)

      case _ =>
    }

    val reporter = ctx.reporter

    val baseFactories = Seq(
      SolverFactory(() => new FairZ3Solver(ctx, program) with TimeoutSolver)
    )

    val solverFactories = timeout match {
      case Some(sec) =>
        baseFactories.map { sf =>
          new TimeoutSolverFactory(sf, sec*1000L)
        }
      case None =>
        baseFactories
    }

    val vctx = VerificationContext(ctx, solverFactories, reporter)

    reporter.debug("Running verification condition generation...")
    val vcs = generateVerificationConditions(reporter, program, functionsToAnalyse)
    checkVerificationConditions(vctx, vcs)
  }
}
