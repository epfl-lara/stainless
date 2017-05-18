/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package termination

import scala.concurrent.duration._
import scala.annotation.tailrec
import solvers._

/**
 * Checks terminations of functions using the ranking function specified in the `decreases`
 * construct. For now, it works only on first-order functions.
 */
trait DecreasesProcessor extends Processor { self =>
  val ordering: OrderingRelation with RelationBuilder {
    val checker: DecreasesProcessor.this.checker.type
  }

  val name: String = "Decreases Processor"

  import ordering._
  import checker._
  import program._
  import program.trees._
  import program.symbols._
  import program.trees.exprOps._

  private val zero = IntegerLiteral(0)
  private val tru = BooleanLiteral(true)

  def run(problem: Problem): Option[Seq[Result]] = {
    val timer = ctx.timers.termination.processors.decreases.start()

    val fds = problem.funDefs
    val fdIds = problem.funSet.map(_.id)

    val res = if (fds.exists { _.measure.isDefined }) {
      val api = getAPI

      // Important:
      // Here, we filter only functions that have a measure. This is sound because of the following reasoning.
      // Functions in the scc that do not have a decrease measure either will be inlined if it is not self recursive.
      // Otherwise, the caller of this function will carry the blame of non-termination.
      val success: Boolean = fds.filter(_.measure.isDefined).forall { fd =>
        val measure = fd.measure.get
        reporter.debug(s"- Now considering `decreases` of ${fd.id.name} @${fd.getPos}...")

        // (a) check if every function in the measure terminates and does not make a recursive call to an SCC.
        val res = !exists {
          case FunctionInvocation(id, _, _) =>
            if (fdIds(id)) {
              reporter.warning(s"==> INVALID: `decreases` has recursive call to ${id.name}.")
              true
            } else if (!checker.terminates(getFunction(id)).isGuaranteed) {
              reporter.warning(s"==> INVALID: `decreases` calls non-terminating function ${id.name}.")
              true
            } else false
          case _ =>
            false
        } (measure) && {
          // (b) check if the measure is well-founded
          def nonNeg(e: Expr): Expr = e.getType match {
            case TupleType(tps) => And(tps.indices.map(i => nonNeg(TupleSelect(e, i + 1))))
            case IntegerType => GreaterEquals(e, IntegerLiteral(0))
            case BVType(size) => GreaterEquals(e, BVLiteral(0, size))
            case tpe => reporter.fatalError("Unexpected measure type: " + tpe)
          }

          api.solveVALID(Implies(fd.precondition.getOrElse(BooleanLiteral(true)), nonNeg(measure))) match {
            case Some(true) => true
            case Some(false) =>
              reporter.warning(s" ==> INVALID: measure is not well-founded in ${fd.id}")
              false
            case None =>
              reporter.warning(s"==> UNKNOWN: measure cannot be proven to be well-founded in ${fd.id}")
              false
          }
        } && {
          // (c) check if the measure decreases for recursive calls
          val inlinedRelations: Set[Relation] = {
            def rec(fd: FunDef, seen: Set[FunDef]): Set[Relation] = getRelations(fd).flatMap { r =>
              val target = r.call.tfd.fd
              if (seen(target)) {
                Set(r)
              } else {
                rec(target, seen + target).map(r compose _)
              }
            }

            rec(fd, Set(fd))
          }

          inlinedRelations.forall { case Relation(_, path, fi @ FunctionInvocation(_, _, args), _) =>
            val callee = fi.tfd
            if (!problem.funSet(callee.fd)) {
              true
            } else if (!callee.measure.isDefined) {
              // here, we cannot prove termination of the function as it calls a self-recursive function
              // without a measure.
              reporter.warning(s" ==> INVALID: calling self-recursive function ${callee.id} with no measure")
              false
            } else {
              val callMeasure = replaceFromSymbols((callee.params zip args).toMap, callee.measure.get)

              if (callMeasure.getType != measure.getType) {
                reporter.warning(s" ==> INVALID: recursive call ${fi.asString} uses a different measure type")
                false
              } else {
                // construct a lexicographic less than check
                val lessPred = measure.getType match {
                  case TupleType(tps) =>
                    val s = tps.size
                    (1 until s).foldRight(LessThan(TupleSelect(callMeasure, s), TupleSelect(measure, s)): Expr) {
                      (i, acc) =>
                        val m1 = TupleSelect(callMeasure, i)
                        val m2 = TupleSelect(measure, i)
                        Or(LessThan(m1, m2), And(Equals(m1, m2), acc))
                    }
                  case _ =>
                    LessThan(callMeasure, measure)
                }

                api.solveVALID(path implies lessPred) match {
                  case Some(true) => true
                  case Some(false) =>
                    reporter.warning(s" ==> INVALID: measure doesn't decrease for the (transitive) call ${fi.asString}")
                    false
                  case None =>
                    reporter.warning(s"==> UNKNOWN: measure cannot be shown to decrease for (transitive) call ${fi.asString}")
                    false
                }
              }
            }
          }
        }

        if (res) reporter.debug(s"==> VALID")
        res
      }

      if (success) {
        Some(fds.map(Cleared))
      } else {
        Some(fds.map(Broken(_, DecreasesFailed)))
      }
    } else {
      None // nothing is cleared here, so other phases will apply
    }

    timer.stop()
    res
  }
}
