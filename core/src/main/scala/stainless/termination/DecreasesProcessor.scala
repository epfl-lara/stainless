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

    //val (fdsWithMeasure, fdsWOMeasure) = fds.partition(_.measure.isDefined)
    // Important:
    // Here, we filter only functions that have a measure. This is sound because of the following reasoning.
    // Functions in the scc that do not have a decrease measure either will be inlined if it is not self recursive.
    // Otherwise, the caller of this function will carry the blame of non-termination.
    val fails: Seq[FailReason] = fds.flatMap { fd =>
      reporter.info(s"- Now considering ${fd.id.name} @${fd.getPos}...")

      val checksRes = fd.measure match {
        case None => true
        case Some(measure) =>
          //reporter.debug(s" ==> ${fd.id.name} has a measure ")
          // perform some sanity checks
          // (a) check if every function in the measure terminates and does not make a recursive call to an SCC.
          !(exists {
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
          }(measure)) && {
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
                false
              case None =>
                reporter.warning(s"==> UNKNOWN: measure cannot be proven to be well-founded")
                false
              case Some(true) => true
            }
          }
      }
      if (!checksRes) {
        Seq(FailStop(fd))
      } else {
        // (c) check if the measure decreases for recursive calls
        // remove certain function invocations from the body
        val recCallsWithPath = collectRecursiveCallsWithPaths(fd.fullBody, fd, problem.funSet)
        val decRes = recCallsWithPath match {
          case None =>
            // here, we cannot prove termination of the function as it calls a recursive function
            Some(TryOther)

          case Some(seq) if seq.isEmpty => None // nothing to verify

          case Some(seq) if fd.measure.isDefined =>
            val measure = fd.measure.get
            seq.foldLeft(None: Option[FailReason]) {
              case (acc @ Some(_), _) => acc
              case (acc, (fi @ FunctionInvocation(id, tps, args), path)) =>
                val callee = fi.tfd
                /*if (!callee.measure.isDefined) {
                  Some(TryOther)
                } else {*/
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
                      Some(FailStop(fd))
                    case None =>
                      reporter.warning(s"==> UNKNOWN: measure cannot be shown to decrease for (transitive) call ${fi.asString}")
                      Some(TryOther)
                  }
                }
            }
          case _ => Some(TryOther)
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
      None // nothing is cleared here, so other phases will apply
    }
  }

  /**
   * This method collects all recursive calls with paths (recursive in the sense of dependency graph). In case the
   * call does not have decrease measure, it inlines the body if it is not self-recusive,
   * and collects the path in the inlined version.
   */
  def collectRecursiveCallsWithPaths(rootExpr: Expr, rootfun: FunDef, scc: Set[FunDef]): Option[Seq[(FunctionInvocation, Path)]] = {

    lazy val analysisInfo = new CFAAnalysisInfo(rootfun)

    def rec(expr: Expr, initPath: Path, seen: Set[FunDef]): Option[Seq[(FunctionInvocation, Path)]] = {

      val recCallsWithPath = transformers.CollectorWithPC(program) {
        case (fi @ FunctionInvocation(id, _, _), path) if scc(getFunction(id)) => (fi, path)
      } collect (expr, initPath)

      val optSeqs = recCallsWithPath map {
        case cp @ (FunctionInvocation(callee, _, _), _) if getFunction(callee).measure.isDefined =>
          Some(Seq(cp))

        // here, the invocation does not have a measure, but may never be invoked (e.g. if it is inside an uninvocable lambda)
        case (fi @ FunctionInvocation(callee, _, _), _) if !analysisInfo.invocableCyclicCalls(fi) =>
          reporter.debug(s" ==> Ignoring the uninvocable recursive call $fi")
          Some(Seq())

        // here, we have seen a self-recursive function without a measure that can be invoked by rootfun
        case (fi @ FunctionInvocation(callee, _, _), _) if seen(getFunction(callee)) =>
          reporter.warning(s" ==> Recursive call $fi does not have attached measures and could be invoked by ${rootfun.id}.")
          None

        // here, we try to inline the callee and see if it is disappears
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

    val transCallers = transitiveCallers(rootfd) // Note that these are queries over dependency graph

    //println("Functions: "+checker.program.symbols.functions)
    val cfa = new CICFA {
      val program: checker.program.type = checker.program
      val rootfunid = rootfd.id
    }
    cfa.analyze() // Note: trait initialization should happen before the fields are used

    // all lamdbas that may possibly be invoked by rootfd
    val appliedLambdas = {
      cfa.locallyAppliedLambdas.toSet ++
        // all lambdas reachable in the dependency graph from the external lambdas should also be considered applied
        cfa.externallyEscapingLambdas.flatMap { l =>
          var llams = Set(l)
          var callees = Set[Identifier]()
          // collect all top level lambdas and callees
          postTraversal {
            case nl: Lambda => llams += nl
            case FunctionInvocation(calleeid, _, _) =>
              callees += calleeid
            case _ =>
          }(l.body)
          // collect all lamdbas in all callees
          callees.foreach { cid =>
            transitiveCallees(getFunction(cid)).foreach { tc =>
              postTraversal {
                case nl: Lambda => llams += nl
                case _          =>
              }(tc.fullBody)
            }
          }
          llams
        }
    }

    val invocableCyclicCalls = {
      def rec(iner: Expr): Set[FunctionInvocation] = iner match {
        case l @ Lambda(_, body) if appliedLambdas(l) =>
          // can recurse into the body of this lambda as it may be applied by rootfd (transitively)
          rec(body)

        case _: Lambda => Set() // do nothing otherwise

        case fi @ FunctionInvocation(calleeid, _, args) if transCallers(getFunction(calleeid)) => // a possible recursive call to rootfd
          Set(fi) ++ (args flatMap rec).toSet

        case Operator(args, _) =>
          (args flatMap rec).toSet
      }
      rec(rootfd.fullBody)
    }

    /*val callsInvokingRootFun: Set[FunctionInvocation] = {
      cfa.locallyAppliedLambdas.flatMap { l => // TODO: why we need casting here?
        // inner function that checks if the Lambda directly invokes rootfd

      }.toSet ++
        cfa.externallyEscapingLambdas.flatMap { l =>
          def rec(iner: Expr): Set[FunctionInvocation] = iner match {
            case fi @ FunctionInvocation(calleeid, _, args) if transCallers(functions(calleeid)) => Set(fi) ++ (args flatMap rec).toSet
            case Operator(args, _) => (args flatMap rec).toSet
          }
          rec(l.body)
        }
    }*/
    //val transCallerIds = transitiveCallers(callsInvokingRootFun.map(_.id).toSet.map((id: Identifier) => getFunction(id))).map(_.id)
  }

}
