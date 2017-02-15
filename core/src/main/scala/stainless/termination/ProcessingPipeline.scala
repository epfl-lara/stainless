/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package termination

import scala.concurrent.duration._
import scala.collection.mutable.{PriorityQueue, Map => MutableMap, Set => MutableSet}

trait ProcessingPipeline extends TerminationChecker with inox.utils.Interruptible { self =>
  import program._
  import program.trees._
  import program.symbols._
  import CallGraphOrderings._

  private[termination] lazy val ignorePosts = ctx.options.findOptionOrDefault(optIgnorePosts)

  trait Problem {
    def funSet: Set[FunDef]
    def funDefs: Seq[FunDef]
    def contains(fd: FunDef): Boolean = funSet(fd)

    override def toString : String = funDefs.map(_.id).mkString("Problem(", ",", ")")
  }

  object Problem {
    def apply(fds: Set[FunDef]): Problem = new Problem {
      val funSet = fds
      lazy val funDefs = funSet.toSeq
    }

    def apply(fds: Seq[FunDef]): Problem = new Problem {
      val funDefs = fds
      lazy val funSet = funDefs.toSet
    }
  }

  ctx.interruptManager.registerForInterrupts(this)

  private var _interrupted: Boolean = false
  private[termination] def interrupted: Boolean = _interrupted

  def interrupt(): Unit = { _interrupted = true }

  sealed abstract class Result(funDef: FunDef)
  case class Cleared(funDef: FunDef) extends Result(funDef)
  case class Broken(funDef: FunDef, args: Seq[Expr]) extends Result(funDef)
  case class MaybeBroken(funDef: FunDef, args: Seq[Expr]) extends Result(funDef)

  protected val processors: List[Processor { val checker: self.type }]

  protected val encoder: ast.TreeTransformer {
    val s: program.trees.type
    val t: stainless.trees.type
  }

  protected implicit val semanticsProvider: inox.SemanticsProvider { val trees: program.trees.type } =
    encodingSemantics(program.trees)(encoder)

  private def solverFactory(transformer: inox.ast.SymbolTransformer { val s: trees.type; val t: trees.type }) = {
    val transformEncoder = inox.ast.ProgramEncoder(program)(transformer)

    object programEncoder extends {
      val sourceProgram: transformEncoder.targetProgram.type = transformEncoder.targetProgram
      val t: stainless.trees.type = stainless.trees
    } with inox.ast.ProgramEncoder {
      val encoder = self.encoder
      object decoder extends ast.TreeTransformer {
        val s: stainless.trees.type = stainless.trees
        val t: trees.type = trees
      }
    }

    val p: transformEncoder.targetProgram.type = transformEncoder.targetProgram
    val timeout = ctx.options.findOption(inox.optTimeout) match {
      case Some(to) => to / 100
      case None => 2.5.seconds
    }

    solvers.SolverFactory
      .getFromSettings(p, options)(programEncoder)(p.getSemantics)
      .withTimeout(timeout)
  }

  private def solverAPI(transformer: inox.ast.SymbolTransformer { val s: trees.type; val t: trees.type }) = {
    inox.solvers.SimpleSolverAPI(solverFactory(transformer))
  }

  private object withoutPosts extends inox.ast.SimpleSymbolTransformer {
    val s: trees.type = trees
    val t: trees.type = trees

    protected def transformFunction(fd: FunDef): FunDef = {
      // When using the loop processor, it helps to ignore postconditions in the
      // current SCC as these will sometimes disallow models otherwise
      val isLoop = problems.headOption.exists {
        case (_, idx) => processorArray(idx).isInstanceOf[LoopProcessor]
      }

      if (isProblem(fd, ignoreSCC = !isLoop) || ignorePosts) {
        fd.copy(fullBody = exprOps.withPostcondition(fd.fullBody, None))
      } else {
        fd
      }
    }

    protected def transformADT(adt: ADTDefinition): ADTDefinition = adt
  }

  private var transformers: inox.ast.SymbolTransformer { val s: trees.type; val t: trees.type } = withoutPosts

  private[termination] def registerTransformer(
    transformer: inox.ast.SymbolTransformer { val s: trees.type; val t: trees.type }
  ): Unit = transformers = transformers andThen transformer

  def solveVALID(e: Expr) = solverAPI(transformers).solveVALID(e)
  def solveVALID(e: Expr, t: inox.ast.SymbolTransformer { val s: trees.type; val t: trees.type }) = {
    solverAPI(transformers andThen t).solveVALID(e)
  }

  def solveSAT(e: Expr) = solverAPI(transformers).solveSAT(e)
  def solveSAT(e: Expr, t: inox.ast.SymbolTransformer { val s: trees.type; val t: trees.type }) = {
    solverAPI(transformers andThen t).solveSAT(e)
  }

  private lazy val processorArray: Array[Processor { val checker: self.type }] = {
    assert(processors.nonEmpty)
    processors.toArray
  }

  implicit private val debugSection = DebugSectionTermination
  private lazy val reporter = ctx.reporter

  implicit object ProblemOrdering extends Ordering[(Problem, Int)] {
    def compare(a: (Problem, Int), b: (Problem, Int)): Int = {
      val comp = componentOrdering.compare(a._1.funSet, b._1.funSet)
      if (comp != 0) {
        comp
      } else {
        val ((aProblem, aIndex), (bProblem, bIndex)) = (a,b)
        val (aDefs, bDefs) = (aProblem.funSet, bProblem.funSet)

        val aCallees: Set[FunDef] = aDefs.flatMap(transitiveCallees)
        val bCallees: Set[FunDef] = bDefs.flatMap(transitiveCallees)

        val smallerPool = bCallees.size compare aCallees.size
        if (smallerPool != 0) {
          smallerPool 
        } else {
          val aCallers: Set[FunDef] = aDefs.flatMap(transitiveCallers)
          val bCallers: Set[FunDef] = bDefs.flatMap(transitiveCallers)

          val largerImpact = aCallers.size compare bCallers.size
          if (largerImpact != 0) largerImpact else {
            bIndex compare aIndex
          }
        }
      }
    }
  }

  private val problems = new PriorityQueue[(Problem, Int)]
  def running = problems.nonEmpty

  private val clearedMap     : MutableMap[FunDef, String]              = MutableMap.empty
  private val brokenMap      : MutableMap[FunDef, (String, Seq[Expr])] = MutableMap.empty
  private val maybeBrokenMap : MutableMap[FunDef, (String, Seq[Expr])] = MutableMap.empty

  private val unsolved     : MutableSet[Problem] = MutableSet.empty
  private val dependencies : MutableSet[Problem] = MutableSet.empty

  def isProblem(fd: FunDef, ignoreSCC: Boolean = false): Boolean = {
    lazy val callees = transitiveCallees(fd)
    lazy val problemDefs = (if (ignoreSCC) problems.drop(1) else problems).flatMap(_._1.funDefs).toSet
    unsolved.exists(_.contains(fd)) ||
    dependencies.exists(_.contains(fd)) || 
    unsolved.exists(_.funDefs exists callees) ||
    dependencies.exists(_.funDefs exists callees) ||
    problemDefs(fd) || (problemDefs intersect callees).nonEmpty
  }

  private def printQueue() {
    val sb = new StringBuilder()
    sb.append("- Problems in Queue:\n")
    for(p @ (problem, index) <- problems) {
      sb.append("  -> Problem awaiting processor #")
      sb.append(index + 1)
      sb.append(" (")
      sb.append(processorArray(index).name)
      sb.append(")")
      if (p == problems.head) sb.append(" <- next")
      sb.append("\n")
      for(funDef <- problem.funDefs) {
        sb.append("      " + funDef.id + "\n")
      }
    }
    reporter.debug(sb.toString)
  }

  private def printResult(results: List[Result]) {
    val sb = new StringBuilder()
    sb.append("- Processing Result:\n")
    for(result <- results) result match {
      case Cleared(fd) => sb.append(f"    ${fd.id}%-10s Cleared\n")
      case Broken(fd, args) => sb.append(f"    ${fd.id}%-10s ${"Broken for arguments: " + args.mkString("(", ",", ")")}\n")
      case MaybeBroken(fd, args) => sb.append(f"    ${fd.id}%-10s ${"HO construct application breaks for arguments: " + args.mkString("(", ",", ")")}\n")
    }
    reporter.debug(sb.toString)
  }

  private val terminationMap : MutableMap[FunDef, TerminationGuarantee] = MutableMap.empty
  def terminates(funDef: FunDef): TerminationGuarantee = {
    val guarantee = {
      terminationMap.get(funDef) orElse
      brokenMap.get(funDef).map { case (reason, args) => LoopsGivenInputs(reason, args) } orElse
      maybeBrokenMap.get(funDef).map { case (reason, args) => MaybeLoopsGivenInputs(reason, args)} getOrElse {
        val callees = transitiveCallees(funDef)
        val broken = brokenMap.keys.toSet ++ maybeBrokenMap.keys
        val brokenCallees = callees intersect broken
        if (brokenCallees.nonEmpty) {
          CallsNonTerminating(brokenCallees)
        } else if (isProblem(funDef)) {
          NoGuarantee
        } else {
          clearedMap.get(funDef).map(Terminates).getOrElse(
            if (interrupted) {
              NoGuarantee
            } else if (!running) {
              val verified = verifyTermination(funDef)
              for (fd <- verified) terminates(fd) // fill in terminationMap
              terminates(funDef)
            } else {
              if (!dependencies.exists(_.contains(funDef))) {
                dependencies ++= generateProblems(funDef)
              }
              NoGuarantee
            }
          )
        }
      }
    }

    if (!running) terminationMap(funDef) = guarantee
    guarantee
  }

  private def generateProblems(funDef: FunDef): Seq[Problem] = {
    val funDefs = transitiveCallees(funDef) + funDef
    val pairs = allCalls.filter { case (fd1, fd2) => funDefs(fd1) && funDefs(fd2) }
    val callGraph = pairs.groupBy(_._1).mapValues(_.map(_._2))
    val allComponents = inox.utils.SCC.scc(callGraph)

    val (problemComponents, nonRec) = allComponents.partition { fds =>
      fds.flatMap(fd => transitiveCallees(fd)) exists fds
    }

    for (fd <- funDefs -- problemComponents.toSet.flatten) clearedMap(fd) = "Non-recursive"
    val newProblems = problemComponents.filter(fds => fds.forall { fd => !terminationMap.isDefinedAt(fd) })
    newProblems.map(fds => Problem(fds.toSeq))
  }

  def verifyTermination(funDef: FunDef): Set[FunDef] = {
    reporter.debug("Verifying termination of " + funDef.id)
    val terminationProblems = generateProblems(funDef)
    problems ++= terminationProblems.map(_ -> 0)

    val it = new Iterator[(String, List[Result])] {
      def hasNext : Boolean      = running
      def next()  : (String, List[Result]) = {
        printQueue()
        val (problem, index) = problems.head
        val processor = processorArray(index)
        reporter.debug("Running " + processor.name)
        val result = processor.run(problem)
        reporter.debug(" +-> " + (if (result.isDefined) "Success" else "Failure")+ "\n")

        // dequeue and enqueue atomically to make sure the queue always
        // makes sense (necessary for calls to terminates(fd))
        problems.dequeue()
        result match {
          case None if index == processorArray.length - 1 =>
            unsolved += problem
          case None =>
            problems.enqueue(problem -> (index + 1))
          case Some(results) =>
            val impacted = problem.funDefs.flatMap(fd => transitiveCallers(fd))
            val reenter = unsolved.filter(p => (p.funDefs intersect impacted).nonEmpty)
            problems.enqueue(reenter.map(_ -> 0).toSeq : _*)
            unsolved --= reenter
        }

        if (dependencies.nonEmpty) {
          problems.enqueue(dependencies.map(_ -> 0).toSeq : _*)
          dependencies.clear
        }

        processor.name -> result.toList.flatten
      }
    }

    for ((reason, results) <- it; result <- results if !interrupted) result match {
      case Cleared(fd) =>
        reporter.info(s"Result for ${fd.id}")
        reporter.info(s" => CLEARED ($reason)")
        clearedMap(fd) = reason
      case Broken(fd, args) =>
        reporter.info(s"Result for ${fd.id}")
        reporter.info(s" => BROKEN (for call ${fd.id}(${args.map(_.asString).mkString(",")})")
        brokenMap(fd) = (reason, args)
      case MaybeBroken(fd, args) =>
        reporter.info(s"Result for ${fd.id}")
        reporter.info(s" => MAYBE BROKEN (for call ${fd.id}(${args.map(_.asString).mkString(",")})")
        maybeBrokenMap(fd) = (reason, args)
    }

    val verified = terminationProblems.flatMap(_.funDefs).toSet.filter(!isProblem(_))
    problems.clear()
    verified
  }
}
