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

  sealed abstract class FailReason
  case object TryOther extends FailReason
  case class FailStop(funDef: FunDef) extends FailReason

  private val zero = IntegerLiteral(0)
  private val tru = BooleanLiteral(true)

  def run(problem: Problem): Option[Seq[Result]] = {

    val fds = problem.funDefs
    val fdIds = problem.funSet.map(_.id)

    //println("Functions with measures: "+fds.filter( _.measure.isDefined).map(_.id))

    if (fds.exists { _.measure.isDefined }) {
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
          // (b) check if the measure is well-founded
          val nonneg = measure.getType match {
            case TupleType(tps) =>
              And((1 to tps.size).map(i => GreaterEquals(TupleSelect(measure, i), zero)))
            case _ =>
              GreaterEquals(measure, zero)
          }
          solveVALID(nonneg) match {
            case Some(false) =>
              reporter.warning(s" ==> INVALID: measure is not well-founded")
              Seq(TryOther)
            case None =>
              reporter.warning(s"==> UNKNOWN: measure cannot be proven to be well-founded")
              Seq(TryOther)
            case Some(true) =>
              // (c) check if the measure decreases for recursive calls
              // remove certain function invocations from the body
              val recCallsWithPath = collectRecursiveCallsWithPaths(fd.fullBody, fd, problem.funSet)
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
   * This method collects all recursive calls with paths (recursive in the sense of dependency graph). In case the
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
        case _                        => None
      }
    }

    rec(rootExpr, Path.empty, Set(rootfun))
  }

  /**
   * We (lazily) perform some analysis here to discover Lambdas which can never cause non-termination
   */
  class CFAAnalysisInfo(rootfd: FunDef) {

    lazy val transCallers = transitiveCallers(rootfd)  // Note that these are queries over dependency graph

    lazy val cfa = new CICFA(program, rootfd.id)
    import cfa.program._
    import cfa.program.trees._

    lazy val lambdasCallingRootFun = {
      cfa.locallyAppliedLambdas.filter{       // TODO: why we need casting here?
        case Lambda(_, body) =>
          // inner function that checks if the Lambda directly invokes rootfd
          def rec(iner: Expr): Boolean = {
            case _ : Lambda => false // we can ignore calls inside lambdas
            case FunctionInvocatoin(calleeid, _, args) =>
               rootfd.id == calleeid ||  (args exists rec)  // a direct call to rootfd is made
            case Operator(args, _) =>
              args exists rec
          }
          rec(body)
      } ++
        cfa.externallyEscapingLambdas.filter{ case Lambda(_, body) =>
          exists {
            case FunctionInvocatoin(calleeid, _, args) => transCallers(functions(calleeid))  // the rootfd can be extracted from this Lambda
            case _ => false
          }(body)
        }
    }

    lazy val transCreators = lambdasCallingRootFun.flatMap(cfa.creators(_)).flatMap(crid => transitiveCallers(getFunction(crid))).map(_.id)

    /*lazy val externallyInvocableRecursiveCalls = { // set of  function calls that invokes callers of rootfd and are invoked within applied lambdas
      collect{
        case l@Lambda(_, body) if externallyAppliedLambdas.contains(l) => // this is a applied lambda
          collect{
            case fi@FunctionInvocation(fid, _, _) if transCallers(functions(fid)) => Set(fi) // fi calls a caller of fd within an applied Lambda
            case _ => Set()
          }(body)
        case _ => Set[FunctionInvocation]()
      }(rootfd.fullBody)
        // TODO: here it suffices to intersect locallyAppliedlambdas with immediately cyclic lambdas and not mutually cyclic lambdas
    }

    def isAppliedCyclicLambda(l: Lambda) = appliedCyclicLambdas(l) // only these Lambdas can cause non-termination
*/
    }
}
