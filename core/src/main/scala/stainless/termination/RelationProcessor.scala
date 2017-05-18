/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package termination

import inox.utils._

trait RelationProcessor extends OrderingProcessor {
  val ordering: OrderingRelation with Strengthener with RelationBuilder {
    val checker: RelationProcessor.this.checker.type
  }

  val name: String = "Relation Processor " + ordering.description

  import checker._
  import ordering._
  import program.trees._
  import program.symbols._

  def run(problem: Problem): Option[Seq[Result]] = {
    val timer = program.ctx.timers.termination.processors.relation.start()

    strengthenPostconditions(problem.funSet)
    strengthenApplications(problem.funSet)

    val formulas = problem.funDefs.map { funDef =>
      funDef -> ordering.getRelations(funDef).collect {
        case Relation(_, path, fi @ FunctionInvocation(_, _, args), _) if problem.funSet(fi.tfd.fd) =>
          val args0 = funDef.params.map(_.toVariable)
          def constraint(expr: Expr) = path implies expr
          val lessThan = ordering.lessThan(args, args0)
          val lessEquals = ordering.lessEquals(args, args0)
          (fi.tfd.fd, (constraint(lessThan), constraint(lessEquals)))
      }
    }

    sealed abstract class Result
    case object Success extends Result
    case class Dep(deps: Set[FunDef]) extends Result
    case object Failure extends Result

    val api = getAPI

    reporter.debug("- Searching for size decrease")
    val decreasing = formulas.map({ case (fd, formulas) =>
      val solved = formulas.map({ case (fid, (gt, ge)) =>
        if (api.solveVALID(gt).contains(true)) Success
        else if (api.solveVALID(ge).contains(true)) Dep(Set(fid))
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
      val (allOk, allNok) = fixpoint[(Set[FunDef], List[(FunDef, Set[FunDef])])] { case (fds, deps) =>
        val (okDeps, nokDeps) = deps.partition({ case (fd, deps) => deps.subsetOf(fds) })
        val newFds = fds ++ okDeps.map(_._1)
        (newFds, nokDeps)
      } ((ok.toSet, nok))

      (allOk, allNok.map(_._1).toSet ++ decreasing.collect({ case (fd, Failure) => fd }))
    }

    assert(terminating ++ nonTerminating == problem.funSet)

    val res = if (nonTerminating.isEmpty) {
      Some(terminating.map(Cleared).toSeq)
    } else {
      None
    }

    timer.stop()
    res
  }
}
