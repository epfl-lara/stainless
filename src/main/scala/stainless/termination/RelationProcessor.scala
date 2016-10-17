/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package termination

import leon.purescala.Expressions._
import leon.purescala.Constructors._
import leon.purescala.Definitions._

class RelationProcessor(
    val checker: TerminationChecker,
    val modules: RelationBuilder with RelationComparator with Strengthener with StructuralSize
  ) extends Processor with Solvable {

  val name: String = "Relation Processor " + modules.comparisonMethod

  def run(problem: Problem): Option[Seq[Result]] = {
    if (!modules.isApplicableFor(problem)) return None
    
    reporter.debug("- Strengthening postconditions")
    modules.strengthenPostconditions(problem.funSet)(this)

    reporter.debug("- Strengthening applications")
    modules.strengthenApplications(problem.funSet)(this)

    val formulas = problem.funDefs.map({ funDef =>
      funDef -> modules.getRelations(funDef).collect({
        case Relation(_, path, FunctionInvocation(tfd, args), _) if problem.funSet(tfd.fd) =>
          val args0 = funDef.params.map(_.toVariable)
          def constraint(expr: Expr) = path implies expr
          val greaterThan = modules.sizeDecreasing(args0, args)
          val greaterEquals = modules.softDecreasing(args0, args)
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
      val (allOk, allNok) = fix(currentReducing, ok.toSet, nok)
      (allOk, allNok.map(_._1).toSet ++ decreasing.collect({ case (fd, Failure) => fd }))
    }

    assert(terminating ++ nonTerminating == problem.funSet)

    if (nonTerminating.isEmpty)
      Some(terminating.map(Cleared).toSeq)
    else
      None
  }
}
