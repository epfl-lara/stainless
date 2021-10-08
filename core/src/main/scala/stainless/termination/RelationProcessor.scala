/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package termination

import inox.utils._

class RelationProcessor(override val checker: ProcessingPipeline)
                       // Alias for checker, as we cannot use it to define ordering
                       (override val chker: checker.type)
                       (override val ordering: OrderingRelation with Strengthener with RelationBuilder {
                         val checker: chker.type
                       })
  extends OrderingProcessor("Relation Processor " + ordering.description, checker, ordering) {

  def this(chker: ProcessingPipeline,
           ordering: OrderingRelation with Strengthener with RelationBuilder {
             val checker: chker.type
           }) =
    this(chker)(chker)(ordering)

  import checker._
  import checker.context._
  import checker.program.trees._
  import checker.program.symbols.{given, _}
  import ordering._

  def run(problem: Problem): Option[Seq[Result]] = timers.termination.processors.relation.run {
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
    val decreasing = formulas.map {
      case (fd, formulas) =>
        val solved = formulas.map {
          case (fid, (gt, ge)) =>
            if (api.solveVALID(gt).contains(true)) Success
            else if (api.solveVALID(ge).contains(true)) Dep(Set(fid))
            else Failure
        }

        val result =
          if (solved.contains(Failure)) Failure
          else {
            val deps = solved.collect { case Dep(fds) => fds }.flatten
            if (deps.isEmpty) Success
            else Dep(deps)
          }
        fd -> result
    }

    val (terminating, nonTerminating) = {
      val ok = decreasing.collect { case (fd, Success) => fd -> IntegerLiteral(0) }
      val nok = decreasing.collect { case (fd, Dep(fds)) => fd -> fds }.toList

      var iteration = 0
      val (allOk, allNok) = fixpoint[(Set[(FunDef, IntegerLiteral)], List[(FunDef, Set[FunDef])])] {
        case (fds, deps) =>
          iteration += 1
          val (okDeps, nokDeps) = deps.partition { case (fd, deps) => deps.subsetOf(fds.map { _._1 }) }
          val newFds = fds ++ okDeps.map { p =>
            (p._1, IntegerLiteral(iteration))
          }
          (newFds, nokDeps)
      } ((ok.toSet, nok))

      (allOk, allNok.map(_._1).toSet ++ decreasing.collect { case (fd, Failure) => fd })
    }

    assert(terminating.map(_._1) ++ nonTerminating == problem.funSet)

    if (nonTerminating.isEmpty) {
      Some(terminating.map { tf =>
        val measure = exprOps.measureOf(tf._1.fullBody) match {
          case Some(measure) => measure
          case None =>
            val induced = ordering.measure(tf._1.params.map { _.toVariable })
            flatten(induced, Seq(tf._2))
        }

        // We preserve the measure specified by the user
        measureCache.add(tf._1 -> measure)
        val inductiveLemmas =
          Some((ordering.getPostconditions, ordering.insertedApps))
        Cleared(tf._1, Some(measure), inductiveLemmas)
      }.toSeq)
    } else {
      None
    }
  }
}
