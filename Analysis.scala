package leon
package verification

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._

import Extensions._

import solvers.{Solver,TrivialSolver}

import scala.collection.mutable.{Set => MutableSet}

class Analysis(val program : Program, val reporter: Reporter) {
  Extensions.loadAll(reporter)

  val analysisExtensions: Seq[Analyser] = loadedAnalysisExtensions

  val trivialSolver = new TrivialSolver(reporter) // This one you can't disable :D

  val solverExtensions: Seq[Solver] = trivialSolver +: loadedSolverExtensions

  solverExtensions.foreach(_.setProgram(program))

  val defaultTactic = new DefaultTactic(reporter)
  defaultTactic.setProgram(program)
  val inductionTactic = new InductionTactic(reporter)
  inductionTactic.setProgram(program)

  // Calling this method will run all analyses on the program passed at
  // construction time. If at least one solver is loaded, verification
  // conditions are generated and passed to all solvers. Otherwise, only the
  // Analysis extensions are run on the program.
  def analyse : VerificationReport = {
    // We generate all function templates in advance.
    for(funDef <- program.definedFunctions if funDef.hasImplementation) {
      // this gets cached :D
      FunctionTemplate.mkTemplate(funDef)
    }

    val report = if(solverExtensions.size > 1) {
      reporter.info("Running verification condition generation...")
      checkVerificationConditions(generateVerificationConditions)
    } else {
      reporter.warning("No solver specified. Cannot test verification conditions.")
      VerificationReport.emptyReport
    }

    analysisExtensions.foreach(ae => {
      reporter.info("Running analysis from extension: " + ae.description)
      ae.analyse(program)
    })

    report
  }

  private def generateVerificationConditions : List[VerificationCondition] = {
    var allVCs: Seq[VerificationCondition] = Seq.empty
    val analysedFunctions: MutableSet[String] = MutableSet.empty

    for(funDef <- program.definedFunctions.toList.sortWith((fd1, fd2) => fd1 < fd2) if (Settings.functionsToAnalyse.isEmpty || Settings.functionsToAnalyse.contains(funDef.id.name))) {
      analysedFunctions += funDef.id.name

      val tactic: Tactic =
        if(funDef.annotations.contains("induct")) {
          inductionTactic
        } else {
          defaultTactic
        }

      if(funDef.body.isDefined) {
        allVCs ++= tactic.generatePreconditions(funDef)
        allVCs ++= tactic.generatePatternMatchingExhaustivenessChecks(funDef)
        allVCs ++= tactic.generatePostconditions(funDef)
        allVCs ++= tactic.generateMiscCorrectnessConditions(funDef)
        allVCs ++= tactic.generateArrayAccessChecks(funDef)
      }
      allVCs = allVCs.sortWith((vc1, vc2) => {
        val id1 = vc1.funDef.id.name
        val id2 = vc2.funDef.id.name
        if(id1 != id2) id1 < id2 else vc1 < vc2
      })
    }

    val notFound: Set[String] = Settings.functionsToAnalyse -- analysedFunctions
    notFound.foreach(fn => reporter.error("Did not find function \"" + fn + "\" though it was marked for analysis."))

    allVCs.toList
  }

  private def checkVerificationConditions(vcs: Seq[VerificationCondition]) : VerificationReport = {
    for(vcInfo <- vcs) {
      val funDef = vcInfo.funDef
      val vc = vcInfo.condition

      reporter.info("Now considering '" + vcInfo.kind + "' VC for " + funDef.id + "...")
      reporter.info("Verification condition (" + vcInfo.kind + ") for ==== " + funDef.id + " ====")
      // if(Settings.unrollingLevel == 0) {
      reporter.info(simplifyLets(vc))
      // } else {
      //   reporter.info("(not showing unrolled VCs)")
      // }

      // try all solvers until one returns a meaningful answer
      var superseeded : Set[String] = Set.empty[String]
      solverExtensions.find(se => {
        reporter.info("Trying with solver: " + se.shortDescription)
        if(superseeded(se.shortDescription) || superseeded(se.description)) {
          reporter.info("Solver was superseeded. Skipping.")
          false
        } else {
          superseeded = superseeded ++ Set(se.superseeds: _*)

          val t1 = System.nanoTime
          se.init()
          val solverResult = se.solve(vc)
          val t2 = System.nanoTime
          val dt = ((t2 - t1) / 1000000) / 1000.0

          solverResult match {
            case None => false
            case Some(true) => {
              reporter.info("==== VALID ====")

              vcInfo.value = Some(true)
              vcInfo.solvedWith = Some(se)
              vcInfo.time = Some(dt)

              true
            }
            case Some(false) => {
              reporter.error("==== INVALID ====")

              vcInfo.value = Some(false)
              vcInfo.solvedWith = Some(se)
              vcInfo.time = Some(dt)

              true
            }
          }
        }
      }) match {
        case None => {
          reporter.warning("No solver could prove or disprove the verification condition.")
        }
        case _ => 
      } 
    
    } 

    val report = new VerificationReport(vcs)
    reporter.info(report.summaryString)
    report
  }
}
