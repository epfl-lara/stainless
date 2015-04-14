/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package termination

import purescala.Expressions._
import purescala.Common._
import purescala.Definitions._

import leon.solvers._
import leon.solvers.z3._

case class Problem(funDefs: Set[FunDef]) {
  override def toString : String = funDefs.map(_.id).mkString("Problem(", ",", ")")
}

sealed abstract class Result(funDef: FunDef)
case class Cleared(funDef: FunDef) extends Result(funDef)
case class Broken(funDef: FunDef, args: Seq[Expr]) extends Result(funDef)
case class MaybeBroken(funDef: FunDef, args: Seq[Expr]) extends Result(funDef)

trait Processor {

  val name: String

  val checker : TerminationChecker

  implicit val debugSection = utils.DebugSectionTermination
  val reporter = checker.context.reporter

  def run(problem: Problem): (Traversable[Result], Traversable[Problem])
}

trait Solvable extends Processor {

  val checker : TerminationChecker with Strengthener with StructuralSize

  private val solver: SolverFactory[Solver] = SolverFactory(() => {
    val program     : Program     = checker.program
    val context     : LeonContext = checker.context
    val sizeModule  : ModuleDef   = ModuleDef(FreshIdentifier("$size"), checker.defs.toSeq, false)
    val sizeUnit    : UnitDef     = UnitDef(FreshIdentifier("$size"),Seq(sizeModule)) 
    val newProgram  : Program     = program.copy( units = sizeUnit :: program.units)

    (new FairZ3Solver(context, newProgram) with TimeoutAssumptionSolver).setTimeout(500L)
  })

  type Solution = (Option[Boolean], Map[Identifier, Expr])

  private def withoutPosts[T](block: => T): T = {
    val dangerousFunDefs = checker.functions.filter(fd => !checker.terminates(fd).isGuaranteed)
    val backups = dangerousFunDefs.toList map { fd =>
      val p = fd.postcondition
      fd.postcondition = None
      () => fd.postcondition = p
    }

    val res : T = block // force evaluation now
    backups.foreach(_())
    res
  }

  def maybeSAT(problem: Expr): Boolean = {
    withoutPosts {
      SimpleSolverAPI(solver).solveSAT(problem)._1 getOrElse true
    }
  }

  def definitiveALL(problem: Expr): Boolean = {
    withoutPosts {
      SimpleSolverAPI(solver).solveSAT(Not(problem))._1.exists(!_)
    }
  }

  def definitiveSATwithModel(problem: Expr): Option[Map[Identifier, Expr]] = {
    withoutPosts {
      val (sat, model) = SimpleSolverAPI(solver).solveSAT(problem)
      if (sat.isDefined && sat.get) Some(model) else None
    }
  }
}

class ProcessingPipeline(program: Program, context: LeonContext, _processors: Processor*) {
  implicit val debugSection = utils.DebugSectionTermination

  import scala.collection.mutable.{Queue => MutableQueue}

  assert(_processors.nonEmpty)
  private val processors: Array[Processor] = _processors.toArray
  private val reporter: Reporter = context.reporter

  implicit object ProblemOrdering extends Ordering[(Problem, Int)] {
    def compare(a: (Problem, Int), b: (Problem, Int)): Int = {
      val ((aProblem, aIndex), (bProblem, bIndex)) = (a,b)
      val (aDefs, bDefs) = (aProblem.funDefs, bProblem.funDefs)

      val aCallees: Set[FunDef] = aDefs.flatMap(program.callGraph.transitiveCallees)
      val bCallees: Set[FunDef] = bDefs.flatMap(program.callGraph.transitiveCallees)

      lazy val aCallers: Set[FunDef] = aDefs.flatMap(program.callGraph.transitiveCallers)
      lazy val bCallers: Set[FunDef] = bDefs.flatMap(program.callGraph.transitiveCallers)

      val aCallsB = bDefs.subsetOf(aCallees)
      val bCallsA = aDefs.subsetOf(bCallees)

      if (aCallsB && !bCallsA) {
        -1
      } else if (bCallsA && !aCallsB) {
        1
      } else {
        val smallerPool = bCallees.size compare aCallees.size
        if (smallerPool != 0) smallerPool else {
          val largerImpact = aCallers.size compare bCallers.size
          if (largerImpact != 0) largerImpact else {
            bIndex compare aIndex
          }
        }
      }
    }
  }

  private val initialProblem : Problem = Problem(program.definedFunctions.toSet)
  private val problems = new scala.collection.mutable.PriorityQueue[(Problem, Int)] += (initialProblem -> 0)
//  private val problems : MutableQueue[(Problem,Int)] = MutableQueue((initialProblem, 0))
  private var unsolved : Set[Problem] = Set()

  private def printQueue() {
    val sb = new StringBuilder()
    sb.append("- Problems in Queue:\n")
    for((problem, index) <- problems) {
      sb.append("  -> Problem awaiting processor #")
      sb.append(index + 1)
      sb.append(" (")
      sb.append(processors(index).name)
      sb.append(")\n")
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

  def clear(fd: FunDef) : Boolean = {
    lazy val unsolvedDefs = unsolved.map(_.funDefs).flatten
    lazy val problemDefs = problems.map({ case (problem, _) => problem.funDefs }).flatten.toSet
    def issue(defs: Set[FunDef]) : Boolean = defs(fd) || (defs intersect program.callGraph.transitiveCallees(fd)).nonEmpty
    ! (issue(unsolvedDefs) || issue(problemDefs))
  }

  def run : Iterator[(String, List[Result])] = new Iterator[(String, List[Result])] {
    // basic sanity check, funDefs shouldn't call themselves in precondition!
    // XXX: it seems like some do...
    // assert(initialProblem.funDefs.forall(fd => !fd.precondition.map({ precondition =>
    //   functionCallsOf(precondition).map(fi => program.transitiveCallees(fi.funDef)).flatten
    // }).flatten.toSet(fd)))

    def hasNext : Boolean      = problems.nonEmpty
    def next()  : (String, List[Result]) = {
      printQueue()
      val (problem, index) = problems.head
      val processor : Processor = processors(index)
      reporter.debug("Running " + processor.name)
      val (_results, nextProblems) = processor.run(problem)
      val results = _results.toList
      printResult(results)

      // dequeue and enqueue atomically to make sure the queue always
      // makes sense (necessary for calls to clear(fd))
      problems.dequeue()
      nextProblems match {
        case x :: xs if x == problem =>
          assert(xs.isEmpty)
          if (index == processors.length - 1) unsolved += x
          else problems.enqueue(x -> (index + 1))
        case list @ x :: xs =>
          problems.enqueue(list.map(p => p -> 0) : _*)
          problems.enqueue(unsolved.map(p => p -> 0).toSeq : _*)
          unsolved = Set()
        case Nil => // no problem => do nothing!
      }

      processor.name -> results.toList
    }
  }
}

// vim: set ts=4 sw=4 et:
