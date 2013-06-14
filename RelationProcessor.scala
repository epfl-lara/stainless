package leon
package termination

import leon.purescala.Trees._
import leon.purescala.TreeOps._
import leon.purescala.TypeTrees._
import leon.purescala.Common._
import leon.purescala.Extractors._
import leon.purescala.Definitions._

class RelationProcessor(checker: TerminationChecker) extends Processor(checker) with Solvable {

  val name: String = "Relation Processor"

  RelationBuilder.init
  RelationComparator.init

  def run(problem: Problem) = {

    strengthenPostconditions(problem.funDefs)

    val formulas = problem.funDefs.map({ funDef =>
      funDef -> RelationBuilder.run(funDef).collect({
        case Relation(_, path, FunctionInvocation(fd, args)) if problem.funDefs(fd) =>
          val (e1, e2) = (Tuple(funDef.args.map(_.toVariable)), Tuple(args))
          def constraint(expr: Expr) = Implies(And(path.toSeq), expr)
          val greaterThan = RelationComparator.sizeDecreasing(e1, e2)
          val greaterEquals = RelationComparator.softDecreasing(e1, e2)
          (fd, (constraint(greaterThan), constraint(greaterEquals)))
      })
    })

    sealed abstract class Result
    case object Success extends Result
    case class Dep(deps: Set[FunDef]) extends Result
    case object Failure extends Result

    initSolvers

    val decreasing = formulas.map({ case (fd, formulas) =>
      val solved = formulas.map({ case (fid, (gt, ge)) =>
        if(isAlwaysSAT(gt)) Success
        else if(isAlwaysSAT(ge)) Dep(Set(fid))
        else Failure
      })
      val result = if(solved.contains(Failure)) Failure else {
        val deps = solved.collect({ case Dep(fds) => fds }).flatten
        if(deps.isEmpty) Success
        else Dep(deps)
      }
      fd -> result
    })

    val (terminating, nonTerminating) = {
      def currentReducing(fds: Set[FunDef], deps: List[(FunDef, Set[FunDef])]): (Set[FunDef], List[(FunDef, Set[FunDef])]) = {
        val (okDeps, nokDeps) = deps.partition({ case (fd, deps) => deps.subsetOf(fds) })
        val newFds = fds ++ okDeps.map(_._1)
        (newFds, nokDeps)
      }

      def fix[A,B](f: (A,B) => (A,B), a: A, b: B): (A,B) = {
        val (na, nb) = f(a, b)
        if(na == a && nb == b) (a,b) else fix(f, na, nb)
      }

      val ok = decreasing.collect({ case (fd, Success) => fd }).toSet
      val nok = decreasing.collect({ case (fd, Dep(fds)) => fd -> fds }).toList
      val (allOk, allNok) = fix(currentReducing, ok, nok)
      (allOk, allNok.map(_._1).toSet ++ decreasing.collect({ case (fd, Failure) => fd }))
    }

    assert(terminating ++ nonTerminating == problem.funDefs)

    val results = terminating.map(Cleared(_)).toList
    val newProblems = if (problem.funDefs intersect nonTerminating nonEmpty) List(Problem(nonTerminating)) else Nil
    (results, newProblems)
  }
}
