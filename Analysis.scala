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

class Analysis(val program : Program, val reporter: Reporter = Settings.reporter) {
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
  def analyse : Unit = {
    // We generate all function templates in advance.
    for(funDef <- program.definedFunctions if funDef.hasImplementation) {
      // this gets cached :D
      FunctionTemplate.mkTemplate(funDef)
    }

    if(solverExtensions.size > 1) {
      reporter.info("Running verification condition generation...")

      val list = generateVerificationConditions
      checkVerificationConditions(list : _*)
    } else {
      reporter.warning("No solver specified. Cannot test verification conditions.")
    }

    analysisExtensions.foreach(ae => {
      reporter.info("Running analysis from extension: " + ae.description)
      ae.analyse(program)
    })
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

  def checkVerificationCondition(vc: VerificationCondition) : Unit = checkVerificationConditions(vc)
  def checkVerificationConditions(vcs: VerificationCondition*) : Unit = {
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

    if(vcs.size > 0) {
      val summaryString = (
        VerificationCondition.infoHeader +
        vcs.map(_.infoLine).mkString("\n", "\n", "\n") +
        VerificationCondition.infoFooter
      )
      reporter.info(summaryString)

      if(Settings.simpleOutput) {
        val outStr =
          if(vcs.forall(_.status == "valid")) "valid" 
          else if(vcs.exists(_.status == "invalid")) "invalid"
          else "unknown"
        println(outStr)
      }

      // Printing summary for the evaluation section of paper:
      val writeSummary = false
      if (writeSummary) {
        def writeToFile(filename: String, content: String) : Unit = {
          try {
            val fw = new java.io.FileWriter(filename)
            fw.write(content)
            fw.close
          } catch {
            case e => reporter.error("There was an error while generating the test file" + filename)
          }
        }

        var toWrite: String = ""
        val functionVCs = vcs groupBy (_.funDef)
        val vcsByPostcond = functionVCs groupBy 
          (_._2 exists ((vc: VerificationCondition) => vc.kind == VCKind.Postcondition))
        def functionInfoLine(id: String, funVCs: Traversable[VerificationCondition]) = {
          val vcsByKind  = funVCs groupBy (_.kind)
          val nbPrecond  = vcsByKind.get(VCKind.Precondition).getOrElse(Nil).size
          val nbMatch    = vcsByKind.get(VCKind.ExhaustiveMatch).getOrElse(Nil).size
          val totalTime  = 
            (funVCs.foldLeft(0.0)((a, b) => a + b.time.getOrElse(0.0)))
          val validStr   = "ok"
          val invalidStr = "err"
          val status = if (funVCs.forall(_.status == "valid")) validStr else invalidStr
          val timeStr = if (totalTime < 0.01) "< 0.01" else ("%-3.2f" format totalTime)

          val toRet =
            "%-25s %-3s %-3s %-9s %6s" format (id, nbPrecond, nbMatch, status, timeStr)
          toRet
        }
        for ((withPostcond, functionsByPostcond) <- vcsByPostcond) {
          if (withPostcond)
            toWrite += "with postcondition:\n"
          else
            toWrite += "without postcondition:\n"
          for ((funDef, funVCs) <- functionsByPostcond.toList.sortWith((p1, p2) => p1._1 < p2._1)) {
            toWrite += functionInfoLine(funDef.id.toString, funVCs) + "\n"
          }
        }

        val fileName = program.mainObject.id.toString + "-evaluation.txt"
        val folderName   = "summary"

        new java.io.File(folderName).mkdir()

        writeToFile(folderName + "/" + fileName, toWrite)
      }
    } else {
      reporter.info("No verification conditions were analyzed.")
    }
  }
}

object Analysis {
  private val keepCallWhenInlined: Boolean = true

  private def defineOneInlining(f : FunctionInvocation) : (Expr, Expr) = {
    val FunctionInvocation(fd, args) = f
    val newLetIDs = fd.args.map(a => FreshIdentifier("arg_" + a.id.name, true).setType(a.tpe)).toList
    val substMap = Map[Expr,Expr]((fd.args.map(_.toVariable) zip newLetIDs.map(Variable(_))) : _*)
    val newBody = replace(substMap, freshenLocals(matchToIfThenElse(fd.body.get)))
    val newFunctionCall = FunctionInvocation(fd, newLetIDs.map(Variable(_))).setType(f.getType)
    val callID = FreshIdentifier("call_" + fd.id.name, true).setType(newBody.getType)
    val callTree = Let(callID, (newLetIDs zip args).foldRight(newBody)((iap, e) => Let(iap._1, iap._2, e)), Variable(callID))

    (Equals(newFunctionCall, Variable(callID)), callTree)
  }

  private def inlineFunctionCall(f : FunctionInvocation) : Expr = {
    val FunctionInvocation(fd, args) = f
    val newLetIDs = fd.args.map(a => FreshIdentifier("arg_" + a.id.name, true).setType(a.tpe)).toList
    val substMap = Map[Expr,Expr]((fd.args.map(_.toVariable) zip newLetIDs.map(Variable(_))) : _*)
    val newBody = replace(substMap, freshenLocals(matchToIfThenElse(fd.body.get)))
    simplifyLets((newLetIDs zip args).foldRight(newBody)((iap, e) => Let(iap._1, iap._2, e)))
  }

  def inlineNonRecursiveFunctions(program: Program, expression: Expr) : Expr = {
    def applyToCall(e: Expr) : Option[Expr] = e match {
      case f @ FunctionInvocation(fd, args) if fd.hasImplementation && !program.isRecursive(fd) => Some(inlineFunctionCall(f))
      case _ => None
    }
  
    var change: Boolean = true
    var toReturn: Expr = expression
    while(change) {
      val (t,c) = searchAndReplaceDFSandTrackChanges(applyToCall)(toReturn)
      change = c
      toReturn = t
    }
    toReturn
  }

  def unrollRecursiveFunctions(program: Program, expression: Expr, times: Int) : Expr = {
    def urf1(expression: Expr, times: Int) : Expr = {
      var newEqs: List[Expr] = Nil

      def applyToCall(e: Expr) : Option[Expr] = e match {
        case f @ FunctionInvocation(fd, args) if fd.hasImplementation && program.isRecursive(fd) => {
          val (newEq, bdy) = defineOneInlining(f)
          newEqs = newEq :: newEqs
          Some(bdy)
        }
        case _ => None
      }

      var remaining = if(times < 0) 0 else times
      var change: Boolean = true
      var toReturn: Expr = expression
      while(remaining > 0 && change) {
        val (t,c) = searchAndReplaceDFSandTrackChanges(applyToCall)(toReturn)
        change = c
        toReturn = inlineNonRecursiveFunctions(program, t)
        remaining = remaining - 1
      }
      liftLets(Implies(And(newEqs.reverse), toReturn))
    }

    def urf2(expression: Expr, times: Int) : Expr = {
      def applyToCall(e: Expr) : Option[Expr] = e match {
        case f @ FunctionInvocation(fd, args) if fd.hasImplementation && program.isRecursive(fd) => Some(inlineFunctionCall(f))
        case _ => None
      }

      var remaining = if(times < 0) 0 else times
      var change: Boolean = true
      var toReturn: Expr = expression
      while(remaining > 0 && change) {
        val (t,c) = searchAndReplaceDFSandTrackChanges(applyToCall)(toReturn)
        change = c
        toReturn = inlineNonRecursiveFunctions(program, t)
        remaining = remaining - 1
      }
      toReturn
    }

    if(keepCallWhenInlined)
      urf1(expression, times)
    else
      urf2(expression, times)
  }

  def inlineContracts(expression: Expr) : Expr = {
    var trueThings: List[Expr] = Nil

    def applyToCall(e: Expr) : Option[Expr] = e match {
      case f @ FunctionInvocation(fd, args) if fd.hasPostcondition => {
        val argsAsLet   = fd.args.map(a => FreshIdentifier("parg_" + a.id.name, true).setType(a.tpe)).toList
        val argsAsLetVars = argsAsLet.map(Variable(_))
        val resultAsLet = FreshIdentifier("call_" + fd.id.name, true).setType(f.getType)
        val newFunCall = FunctionInvocation(fd, argsAsLetVars)
        val substMap = Map[Expr,Expr]((fd.args.map(_.toVariable) zip argsAsLetVars) : _*) + (ResultVariable() -> Variable(resultAsLet))
        // this thing is full of let variables! We will need to lift the let
        // defs. later to make sure they capture this
        val trueFact = replace(substMap, freshenLocals(fd.postcondition.get))
        val defList: Seq[(Identifier,Expr)] = ((argsAsLet :+ resultAsLet) zip (args :+ newFunCall))
        trueThings = trueFact :: trueThings
        // again: these let defs. need eventually to capture the "true thing"
        Some(defList.foldRight[Expr](Variable(resultAsLet))((iap, e) => Let(iap._1, iap._2, e)))
      }
      case _ => None
    }
    val result = searchAndReplaceDFS(applyToCall)(expression)
    liftLets(Implies(And(trueThings.reverse), result))
  }
}
