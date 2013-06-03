/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package verification

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._

import solvers.{Solver,TrivialSolver,TimeoutSolver}
import solvers.z3.FairZ3Solver

import scala.collection.mutable.{Set => MutableSet}

object AnalysisPhase extends LeonPhase[Program,VerificationReport] {
  val name = "Analysis"
  val description = "Leon Verification"

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

    for(funDef <- program.definedFunctions.toList.sortWith((fd1, fd2) => fd1 < fd2) if (functionsToAnalyse.isEmpty || functionsToAnalyse.contains(funDef.id.name))) {

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

    for((funDef, vcs) <- vcs.toSeq.sortWith((a,b) => a._1 < b._1); vcInfo <- vcs if !vctx.shouldStop.get()) {
      val funDef = vcInfo.funDef
      val vc = vcInfo.condition

      reporter.info("Now considering '" + vcInfo.kind + "' VC for " + funDef.id + "...")
      reporter.info("Verification condition (" + vcInfo.kind + ") for ==== " + funDef.id + " ====")
      reporter.info(simplifyLets(vc))

      // try all solvers until one returns a meaningful answer
      var superseeded : Set[String] = Set.empty[String]
      solvers.find(se => {
        reporter.info("Trying with solver: " + se.name)
        if(superseeded(se.name) || superseeded(se.description)) {
          reporter.info("Solver was superseeded. Skipping.")
          false
        } else {
          superseeded = superseeded ++ Set(se.superseeds: _*)

          val t1 = System.nanoTime
          se.init()
          val (satResult, counterexample) = se.solveSAT(Not(vc))
          val solverResult = satResult.map(!_)

          val t2 = System.nanoTime
          val dt = ((t2 - t1) / 1000000) / 1000.0

          solverResult match {
            case _ if vctx.shouldStop.get() =>
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
              vcInfo.solvedWith = Some(se)
              vcInfo.time = Some(dt)
              true

            case Some(false) =>
              reporter.error("Found counter-example : ")
              reporter.error(counterexample.toSeq.sortBy(_._1.name).map(p => p._1 + " -> " + p._2).mkString("\n"))
              reporter.error("==== INVALID ====")
              vcInfo.hasValue = true
              vcInfo.value = Some(false)
              vcInfo.solvedWith = Some(se)
              vcInfo.counterExample = Some(counterexample)
              vcInfo.time = Some(dt)
              true

          }
        }
      }) match {
        case None => {
          vcInfo.hasValue = true
          reporter.warning("No solver could prove or disprove the verification condition.")
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

    val trivialSolver = new TrivialSolver(ctx)
    val fairZ3 = new FairZ3Solver(ctx)

    val solvers0 : Seq[Solver] = trivialSolver :: fairZ3 :: Nil
    val solvers: Seq[Solver] = timeout match {
      case Some(t) => solvers0.map(s => new TimeoutSolver(s, 1000L * t))
      case None => solvers0
    }

    solvers.foreach(_.setProgram(program))

    val vctx = VerificationContext(ctx, solvers, reporter)

    val report = if(solvers.size > 1) {
      reporter.info("Running verification condition generation...")
      val vcs = generateVerificationConditions(reporter, program, functionsToAnalyse)
      checkVerificationConditions(vctx, vcs)
    } else {
      reporter.warning("No solver specified. Cannot test verification conditions.")
      VerificationReport.emptyReport
    }

    report
  }
}
