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
trait DecreasesProcessor extends Processor {

  val name: String = "Decreases Processor"

  import checker._
  import program._
  import program.trees._
  import program.symbols._
  import program.trees.exprOps._

  /**
   * Check that there are no visible functions using application.
   * Note: creating lambdas without using them is harmless. They are just like
   * data structure creation.
   */
  /*private val hasClosures = checker.functions.filterNot(_.annotations contains "library").exists { fd =>
    Seq(fd.fullBody, fd.decreaseMeasure.getOrElse(tru)).exists(exists {
      case app: Application => true
      case _                => false
    } _)
  }*/

  // TODO: Should we remove cached predicate before giving it to the solver ?
  def run(problem: Problem): Option[Seq[Result]] = {
    val fds = problem.funDefs
    val fdIds = problem.funSet.map(_.id)

    //println("Functions with measures: "+fds.filter( _.measure.isDefined).map(_.id))

    if (fds.exists { _.measure.isDefined }) {
      /*if (hasClosures) {
        reporter.error("Cannot use `decreases` in the presence of first-class functions")
        return None
      }*/

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
          // (b) check if the measure decreases for recursive calls
          // remove certain function invocations from the body
          collectRecursiveCallsWithPaths(fd.fullBody, fd, problem.funSet) match {
            case None =>
              // here, we cannot prove termination of the function as it calls a recursive function
              reporter.warning(s" ==> INVALID: not all cycles in the SCC have attached measures")
              false

            case Some(seq) => seq.forall { case (fi @ FunctionInvocation(id, tps, args), path) =>
              val callee = fi.tfd
              if (!callee.measure.isDefined) {
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

                  solveVALID(path implies lessPred) match {
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
      None
    }
  }

  /**
   * This method collects all recusive calls with paths. In case the
   * call does not have decrease measure, it inlines the body if it is not self-recusive,
   * and collects the path in the inlined version.
   */
  def collectRecursiveCallsWithPaths(rootExpr: Expr, rootfun: FunDef, scc: Set[FunDef]): Option[Seq[(FunctionInvocation, Path)]] = {

    def rec(expr: Expr, initPath: Path, seen: Set[FunDef]): Option[Seq[(FunctionInvocation, Path)]] = {

      val recCallsWithPath = transformers.CollectorWithPC(program) {
        case (fi @ FunctionInvocation(id, _, _), path) if scc(getFunction(id)) => (fi, path)
      } collect (expr, initPath)

      val optSeqs = recCallsWithPath map {
        case cp @ (FunctionInvocation(callee, _, _), _) if getFunction(callee).measure.isDefined =>
          Some(Seq(cp))
        case cp @ (FunctionInvocation(callee, _, _), _) if seen(getFunction(callee)) =>
          None
        case (fi @ FunctionInvocation(callee, tps, args), path) =>
          // here the recursive call does not have a measure but is not self recursive
          // inline the recursive call and get the path to the recursive calls in the body
          val tfd = fi.tfd
          val inlined = replaceFromSymbols((tfd.params zip args).toMap, tfd.fullBody)
          rec(inlined, path, seen + tfd.fd)
      }

      optSeqs.foldLeft(Some(Seq.empty): Option[Seq[(FunctionInvocation, Path)]]) {
        case (Some(seq1), Some(seq2)) => Some(seq1 ++ seq2)
        case _ => None
      }
    }

    rec(rootExpr, Path.empty, Set(rootfun))
  }
}
