package leon
package termination

import purescala.Trees._
import purescala.TreeOps._
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

abstract class Processor(val checker: TerminationChecker) {

  val name: String

  def run(problem: Problem): (TraversableOnce[Result], TraversableOnce[Problem])
}

class Solution(solution: Option[Boolean], val model: Map[Identifier, Expr]) {
  lazy val isValid : Boolean = solution getOrElse false
}

object NoSolution extends Solution(None, Map())

object Solution {
  def unapply(s: Solution): Option[(Boolean, Map[Identifier, Expr])] = {
    if (s == NoSolution) None
    else Some(s.isValid, s.model)
  }
}

object Solvable {
  import scala.collection.mutable.{Set => MutableSet}

  private val strengthened : MutableSet[FunDef] = MutableSet()
  private def strengthenPostcondition(funDef: FunDef, cmp: (Expr, TypedExpr) => Expr)
                                     (implicit solver: Processor with Solvable) : Boolean = if (!funDef.hasBody) false else {
    assert(solver.checker.terminates(funDef).isGuaranteed)

    val postcondition = funDef.postcondition
    val args = funDef.args.map(_.toVariable)
    val typedResult = TypedExpr(ResultVariable(), funDef.returnType)
    val sizePost = cmp(Tuple(args), typedResult)
    funDef.postcondition = Some(And(postcondition.toSeq :+ sizePost))

    val prec = matchToIfThenElse(funDef.precondition.getOrElse(BooleanLiteral(true)))
    val post = matchToIfThenElse(funDef.postcondition.get)
    val body = matchToIfThenElse(funDef.body.get)
    val resFresh = FreshIdentifier("result", true).setType(body.getType)
    val formula = Implies(prec, Let(resFresh, body, replace(Map(ResultVariable() -> Variable(resFresh)), post)))

    if (!solver.solve(formula).isValid) {
      funDef.postcondition = postcondition
      strengthened.add(funDef)
      false
    } else {
      strengthened.add(funDef)
      true
    }
  }

  def strengthenPostconditions(funDefs: Set[FunDef])(implicit solver: Processor with Solvable) {
    // Strengthen postconditions on all accessible functions by adding size constraints
    val callees : Set[FunDef] = funDefs.map(fd => solver.checker.program.transitiveCallees(fd)).flatten
    val sortedCallees : Seq[FunDef] = callees.toSeq.sortWith((fd1, fd2) => solver.checker.program.transitivelyCalls(fd2, fd1))
    for (funDef <- sortedCallees if !strengthened(funDef) && funDef.hasBody && solver.checker.terminates(funDef).isGuaranteed) {
      // test if size is smaller or equal to input
      val weekConstraintHolds = strengthenPostcondition(funDef, RelationComparator.softDecreasing)

      if (weekConstraintHolds) {
        // try to improve postcondition with strictly smaller
        strengthenPostcondition(funDef, RelationComparator.sizeDecreasing)
      }
    }
  }
}

trait Solvable { self: Processor =>

  def strengthenPostconditions(funDefs: Set[FunDef]) = Solvable.strengthenPostconditions(funDefs)(this)

  def solve(problem: Expr): Solution = {
    val program     : Program         = self.checker.program
    val allDefs     : Seq[Definition] = program.mainObject.defs ++ StructuralSize.defs
    val newProgram  : Program         = program.copy(mainObject = program.mainObject.copy(defs = allDefs))

    val solvers0 = new TrivialSolver(self.checker.context) :: new FairZ3Solver(self.checker.context) :: Nil
    val solvers = solvers0.map(new TimeoutSolver(_, 500))
    solvers.foreach(_.setProgram(newProgram))

    // drop functions from constraints that might not terminate (and may therefore
    // make Leon unroll them forever...)
    val dangerousCallsMap : Map[Expr, Expr] = functionCallsOf(problem).collect({
      // extra definitions (namely size functions) are quaranteed to terminate because structures are non-looping
      case fi @ FunctionInvocation(fd, args) if !StructuralSize.defs(fd) && !self.checker.terminates(fd).isGuaranteed =>
        fi -> FreshIdentifier("noRun", true).setType(fi.getType).toVariable
    }).toMap

    val expr = searchAndReplace(dangerousCallsMap.get, recursive=false)(problem)

    object Solved {
      var superseeded : Set[String] = Set.empty[String]
      def unapply(se: Solver): Option[Solution] = {
        if(superseeded(se.name) || superseeded(se.description)) {
          None
        } else {
          superseeded = superseeded ++ Set(se.superseeds: _*)

          se.init()
          val (satResult, model) = se.solveSAT(Not(expr))
          val solverResult = satResult.map(!_)

          if (!solverResult.isDefined) None
          else Some(new Solution(solverResult, model))
        }
      }
    }

    solvers.collectFirst({ case Solved(result) => result }) getOrElse NoSolution
  }
}

class ProcessingPipeline(program: Program, context: LeonContext, _processors: Processor*) {
  import scala.collection.mutable.{Queue => MutableQueue}

  assert(_processors.nonEmpty)
  private val processors: Array[Processor] = _processors.toArray
  private val reporter: Reporter = context.reporter

  private val initialProblem : Problem = Problem(program.definedFunctions.toSet)
  private val problems : MutableQueue[(Problem,Int)] = MutableQueue((initialProblem, 0))
  private var unsolved : Set[Problem] = Set()

  private def printQueue {
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
    reporter.info(sb.toString)
  }

  private def printResult(results: List[Result]) {
    val sb = new StringBuilder()
    sb.append("- Queue.head Processing Result:\n")
    for(result <- results) result match {
      case Cleared(fd) => sb.append("    %-10s %s\n".format(fd.id, "Cleared"))
      case Broken(fd, args) => sb.append("    %-10s %s\n".format(fd.id, "Broken for arguments: " + args.mkString("(", ",", ")")))
    }
    reporter.info(sb.toString)
  }

  def clear(fd: FunDef) : Boolean = {
    lazy val unsolvedDefs = unsolved.map(_.funDefs).flatten.toSet
    lazy val problemDefs = problems.map({ case (problem, _) => problem.funDefs }).flatten.toSet
    def issue(defs: Set[FunDef]) : Boolean = defs(fd) || (defs intersect program.transitiveCallees(fd) nonEmpty)
    ! (issue(unsolvedDefs) || issue(problemDefs))
  }

  def run : Iterator[(String, List[Result])] = new Iterator[(String, List[Result])] {
    // basic sanity check, funDefs can't call themselves in precondition!
    assert(initialProblem.funDefs.forall(fd => !fd.precondition.map({ precondition =>
      functionCallsOf(precondition).map(fi => program.transitiveCallees(fi.funDef)).flatten
    }).flatten.toSet(fd)))

    def hasNext : Boolean      = problems.nonEmpty
    def next    : (String, List[Result]) = {
      printQueue
      val (problem, index) = problems.head
      val processor : Processor = processors(index)
      val (_results, nextProblems) = processor.run(problem)
      val results = _results.toList
      printResult(results)

      // dequeue and enqueue atomically to make sure the queue always
      // makes sense (necessary for calls to clear(fd))
      problems.dequeue
      nextProblems match {
        case x :: xs if x == problem =>
          assert(xs.isEmpty)
          if (index == processors.size - 1) unsolved += x
          else problems.enqueue(x -> (index + 1))
        case list @ x :: xs =>
          problems.enqueue(list.map(p => (p -> 0)) : _*)
          problems.enqueue(unsolved.map(p => (p -> 0)).toSeq : _*)
          unsolved = Set()
        case Nil => // no problem => do nothing!
      }

      processor.name -> results.toList
    }
  }
}

// vim: set ts=4 sw=4 et:
