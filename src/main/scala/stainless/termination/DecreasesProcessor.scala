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

  sealed abstract class FailReason
  case object TryOther extends FailReason
  case class FailStop(funDef: FunDef) extends FailReason

  // TODO: Should we remove cached predicate before giving it to the solver ?
  def run(problem: Problem): Option[Seq[Result]] = {
    val fds = problem.funDefs
    val fdIds = problem.funSet.map(_.id)

    if (fds.exists { _.measure.isDefined }) {
      /*if (hasClosures) {
        reporter.error("Cannot use `decreases` in the presence of first-class functions")
        return None
      }*/

      // Important:
      // Here, we filter only functions that have a measure. This is sound because of the following reasoning.
      // Functions in the scc that do not have a decrease measure either will be inlined if it is not self recursive.
      // Otherwise, the caller of this function will carry the blame of non-termination.
      val fails: Seq[FailReason] = fds.filter(_.measure.isDefined).flatMap { fd =>
        val measure = fd.measure.get
        reporter.debug(s"- Now considering `decreases` of ${fd.id.name} @${fd.getPos}...")
        // (a) check if every function in the measure terminates and does not make a recursive call to an SCC.
        if (exists {
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
        }(measure)) {
          Seq(FailStop(fd))
        } else {
          // (b) check if the measure decreases for recursive calls
          // remove certain function invocations from the body
          val recCallsWithPath = collectRecursiveCallsWithPaths(fd.fullBody, problem.funSet)
          val decRes = recCallsWithPath match {
            case None =>
              // here, we cannot prove termination of the function as it calls a recursive function
              reporter.warning(s" ==> INVALID: not all cycles in the SCC have attached measures")
              Some(TryOther)
            case Some(seq) => seq.foldLeft(None: Option[FailReason]) {
              case (acc @ Some(_), _) => acc
              case (acc, (fi @ FunctionInvocation(id, tps, args), path)) =>
                val callee = fi.tfd
                if (!callee.measure.isDefined) {
                  // here, we cannot prove termination of the function as it calls a self-recursive function
                  // without a measure.
                  Some(TryOther)
                } else {
                  val callMeasure = replaceFromSymbols((callee.params zip args).toMap, callee.measure.get)

                  if (callMeasure.getType != measure.getType) {
                    reporter.warning(s" ==> INVALID: recursive call ${fi.asString} uses a different measure type")
                    Some(TryOther)
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
                      case Some(true) => None
                      case Some(false) =>
                        reporter.warning(s" ==> INVALID: measure doesn't decrease for the (transitive) call ${fi.asString}")
                        Some(TryOther)
                      case None =>
                        reporter.warning(s"==> UNKNOWN: measure cannot be shown to decrease for (transitive) call ${fi.asString}")
                        Some(TryOther)
                    }
                  }
                }
            }
          }

          if (decRes.isEmpty) reporter.debug(s"==> VALID")
          decRes.toSeq
        }
      }

      if (fails.isEmpty) {
        Some(fds.map(Cleared))
      } else if (fails.exists(_.isInstanceOf[FailStop])) {
        //reporter.warning(s"Termiantion failed for SCC: ${fds.map(_.id.name).mkString(",")}")
        Some(fds.map(Broken(_, Seq())))
      } else {
        None
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
  def collectRecursiveCallsWithPaths(rootExpr: Expr, scc: Set[FunDef]): Option[Seq[(FunctionInvocation, Path)]] = {
    def rec(expr: Expr, initPath: Path, seen: Set[FunDef]): Option[Seq[(FunctionInvocation, Path)]] = {
      val recCallsWithPath = transformers.CollectorWithPC(program) {
        case (fi @ FunctionInvocation(id, _, _), path) if scc(getFunction(id)) => (fi, path)
      } collect (rootExpr, initPath)

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

    rec(rootExpr, Path.empty, Set.empty)
  }
}
