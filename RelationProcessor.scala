/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package termination

import leon.purescala.Expressions._
import leon.purescala.ExprOps._
import leon.purescala.Types._
import leon.purescala.Common._
import leon.purescala.Extractors._
import leon.purescala.Constructors._
import leon.purescala.Definitions._

class RelationProcessor(
    val checker: TerminationChecker with RelationBuilder with RelationComparator with Strengthener with StructuralSize
  ) extends Processor with Solvable {

  val name: String = "Relation Processor"

  def run(problem: Problem) = {
    reporter.debug("- Strengthening postconditions")
    checker.strengthenPostconditions(problem.funDefs)(this)

    reporter.debug("- Strengthening applications")
    checker.strengthenApplications(problem.funDefs)(this)

    val formulas = problem.funDefs.map({ funDef =>
      funDef -> checker.getRelations(funDef).collect({
        case Relation(_, path, FunctionInvocation(tfd, args), _) if problem.funDefs(tfd.fd) =>
          val (e1, e2) = (tupleWrap(funDef.params.map(_.toVariable)), tupleWrap(args))
          def constraint(expr: Expr) = implies(andJoin(path.toSeq), expr)
          val greaterThan = checker.sizeDecreasing(e1, e2)
          val greaterEquals = checker.softDecreasing(e1, e2)
          (tfd.fd, (constraint(greaterThan), constraint(greaterEquals)))
      })
    })

    sealed abstract class Result
    case object Success extends Result
    case class Dep(deps: Set[FunDef]) extends Result
    case object Failure extends Result

    reporter.debug("- Searching for structural size decrease")
    val decreasing = formulas.map({ case (fd, formulas) =>
      val solved = formulas.map({ case (fid, (gt, ge)) =>
        if (definitiveALL(gt)) Success
        else if (definitiveALL(ge)) Dep(Set(fid))
        else Failure
      })
      val result = if(solved.contains(Failure)) Failure else {
        val deps = solved.collect({ case Dep(fds) => fds }).flatten
        if (deps.isEmpty) Success
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

      val ok = decreasing.collect({ case (fd, Success) => fd })
      val nok = decreasing.collect({ case (fd, Dep(fds)) => fd -> fds }).toList
      val (allOk, allNok) = fix(currentReducing, ok, nok)
      (allOk, allNok.map(_._1).toSet ++ decreasing.collect({ case (fd, Failure) => fd }))
    }

    assert(terminating ++ nonTerminating == problem.funDefs)

    val results = terminating.map(Cleared).toList
    val newProblems = if ((problem.funDefs intersect nonTerminating).nonEmpty) List(Problem(nonTerminating)) else Nil
    (results, newProblems)
  }
}
