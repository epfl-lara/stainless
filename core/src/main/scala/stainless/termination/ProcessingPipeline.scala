/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package termination

import scala.concurrent.duration._
import scala.collection.mutable.{PriorityQueue, Map => MutableMap, Set => MutableSet}

import scala.language.existentials

trait ProcessingPipeline extends TerminationChecker with inox.utils.Interruptible { self =>
  import context._
  import program._
  import program.trees._
  import program.symbols._
  import CallGraphOrderings._

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

  private val dtChecker = new {
    val checker: self.type = self
  } with DatatypeChecker

  interruptManager.registerForInterrupts(this)

  private var _interrupted: Boolean = false
  private[termination] def interrupted: Boolean = _interrupted

  def interrupt(): Unit = { _interrupted = true }

  sealed abstract class Result(funDef: FunDef)
  case class Cleared(funDef: FunDef) extends Result(funDef)
  case class Broken(funDef: FunDef, reason: NonTerminating) extends Result(funDef)

  protected val processors: List[Processor { val checker: self.type }]

  private lazy val processorArray: Array[Processor { val checker: self.type }] = {
    assert(processors.nonEmpty)
    processors.toArray
  }

  implicit private val debugSection = DebugSectionTermination

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
  private var running: Boolean = false

  private val clearedMap     : MutableMap[FunDef, String]                   = MutableMap.empty
  private val brokenMap      : MutableMap[FunDef, (String, NonTerminating)] = MutableMap.empty

  private val unsolved     : MutableSet[Problem] = MutableSet.empty
  private val dependencies : MutableSet[Problem] = MutableSet.empty

  def isProblem(fd: FunDef): Boolean = {
    lazy val callees = transitiveCallees(fd)
    lazy val problemDefs = problems.flatMap(_._1.funDefs).toSet
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
    for (result <- results) result match {
      case Cleared(fd) => sb.append(f"    ${fd.id}%-10s Cleared\n")
      case Broken(fd, reason) => sb.append(f"    ${fd.id}%-10s ${"Broken with reason: " + reason}\n")
    }
    reporter.debug(sb.toString)
  }

  private val terminationCache : MutableMap[FunDef, TerminationGuarantee] = MutableMap.empty
  def terminates(fd: FunDef): TerminationGuarantee = terminationCache.get(fd) match {
    case Some(guarantee) => guarantee
    case None =>
      val callees = transitiveCallees(fd)
      val guarantee: TerminationGuarantee = if (brokenMap contains fd) {
        brokenMap(fd)._2
      } else if ((callees intersect brokenMap.keySet).nonEmpty) {
        CallsNonTerminating(callees intersect brokenMap.keySet)
      } else if (isProblem(fd)) {
        NoGuarantee
      } else if (clearedMap contains fd) {
        Terminates(clearedMap(fd))
      } else if (interrupted) {
        NoGuarantee
      } else if (running) {
        dependencies ++= generateProblems(fd)
        NoGuarantee
      } else {
        runPipeline(fd)
      }
      if (!running) terminationCache(fd) = guarantee
      guarantee
  }

  private def processResult(result: Result, reason: String): Unit = result match {
    case Cleared(fd) =>
      reporter.info(s"Result for ${fd.id}")
      reporter.info(s" => CLEARED ($reason)")
      clearedMap(fd) = reason
    case Broken(fd, msg) =>
      reporter.warning(s"Result for ${fd.id}")
      reporter.warning(s" => BROKEN ($reason)")
      reporter.warning("  " + msg.asString.replaceAll("\n", "\n  "))
      brokenMap(fd) = (reason, msg)
  }

  private def generateProblems(funDef: FunDef): Seq[Problem] = {
    val funDefs = transitiveCallees(funDef) + funDef
    val pairs = allCalls.flatMap { case (id1, id2) =>
      val (fd1, fd2) = (symbols.getFunction(id1), symbols.getFunction(id2))
      if (funDefs(fd1) && funDefs(fd2)) Some(fd1 -> fd2) else None
    }

    val callGraph = pairs.groupBy(_._1).mapValues(_.map(_._2))
    val allComponents = inox.utils.SCC.scc(callGraph)

    val notWellFormed = (for (fd <- funDefs; reason <- dtChecker check fd) yield {
      processResult(Broken(fd, reason), "WF-checker")
      fd
    }).toSet

    val problemComponents = allComponents.filter { fds =>
      fds.flatMap(fd => transitiveCallees(fd)) exists fds
    }

    for (fd <- funDefs -- notWellFormed -- problemComponents.flatten) {
      processResult(Cleared(fd), "Non-recursive")
    }

    val newProblems = problemComponents.filter(fds => fds.forall { fd =>
      !(terminationCache contains fd) && !(brokenMap contains fd)
    })

    // Consider @unchecked functions as terminating.
    val (uncheckedProblems, toCheck) = newProblems.partition(_.forall(_.flags contains Unchecked))
    for (fd <- uncheckedProblems.toSet.flatten) {
      processResult(Cleared(fd), "Unchecked")
    }

    toCheck.map(fds => Problem(fds.toSeq))
  }

  private def runPipeline(fd: FunDef): TerminationGuarantee = {
    reporter.debug("Running termination pipeline for " + fd.id)
    problems ++= generateProblems(fd).map(_ -> 0)

    val it = new Iterator[(String, List[Result])] {
      def hasNext : Boolean      = problems.nonEmpty
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

    running = true
    for ((reason, results) <- it; result <- results if !interrupted) processResult(result, reason)
    running = false
    terminates(fd)
  }
}
