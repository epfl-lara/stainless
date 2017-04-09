/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package termination

import scala.concurrent.duration._
import scala.annotation.tailrec
import scala.collection._
import scala.collection.mutable.{ Map => MutableMap, Set => MutableSet }

import trees._
/**
 * A context-insensitive control-flow analysis that computes
 * the closures that are passed to call backs of given function.
 */
trait CICFA { 
  
  val program: Program { val trees: Trees }
  
  import program._
  import program.trees._
  import program.symbols._
  import program.trees.exprOps._
  
  val rootfun: program.trees.FunDef
  
  // Abstract values and closures
  sealed abstract class AbsValue 
//  {
//    def greaterEquals(other: AbsValue): Boolean
//  }
  case class Closure(lam: program.trees.Lambda) extends AbsValue 
//    env: AbsEnv
//    def greaterEquals(other: AbsValue) = other match {
//      case Closure(lam2, env2) => lam2 == lam && env.greater(env2)
//      case _ => false
//    }    
//    override def hashCode = lam.hashCode // this works also for >= check
//  }
  case class External() extends AbsValue 
//  {
//    def greaterEquals(other: AbsValue) = other.isInstanceOf[External]
//  }
  
  case class AbsEnv(store: Map[Variable,Set[AbsValue]]) { // mapping from a set of live variables to their value
    // checks if this >= AbsElem
    def greaterEquals(other: AbsEnv): Boolean = {
      other.store.forall { (k,v) => store.contains(k) && 
        other.store(k).subsetOf(store(k))
      }
    }
    
    def join(other: AbsEnv): AbsEnv = {
      val ikeys = store.keySet.intersect(other.store.keySet)
      AbsEnv((store.keySet ++ other.store.keyset).map{ 
        case v if ikeys(v) => (v -> (store(v) ++ other.store(v)))
        case v if store.contains(v) => (v -> store(v))
        case v if other.store.contains(v) => (v -> other.store(v))
      })       
    }
  }
   
  case class Summary(in: AbsEnv, out: AbsEnv) {
    def get(fact: AbsEnv): Option[AbsEnv] = {
      if(in.greaterEquals(fact))  Some(out) else None
    }
  }
  
  val tabulation = MutableMap[program.trees.FunDef, Summary] // summary of each function
  val callers = Map[FunDef, Set[FunDef]]
  
  // initialize summaries to identity function from bot to bot 
  program.definedFunctions.foreach { fd: FunDef => 
    val bot = AbsEnv(fd.params.map { vd => vd.id.toVariable -> Set[AbsValue]() })
    tabulation += (fd -> Summary(bot, bot))    
  }
  
  val worklist = List(rootfun)
  
  // iteratively process functions from the worklist.
  // (a) at every function call, join the arguments passed in with the in fact in the summary
  //       -- if the join results in a greater value, add the function back to the worklist  
  // (b) use the summary in the tabulation to complete the intra-procedural analysis
  // (c) Update the caller information on seeing a function call.
  // (d) if the return value of the function is found to be different from the return value in the tabulation   
  //       -- update the entry in the tabulation to a the new value
  //       -- add all callers of the function to the worklist
  // Repeat this until a fix point is reached
  
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
        case _                        => None
      }
    }

    rec(rootExpr, Path.empty, Set(rootfun))
  }
}
