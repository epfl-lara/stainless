/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package termination

import scala.concurrent.duration._
import scala.annotation.tailrec
import scala.collection._
import mutable.{ Map => MutableMap, Set => MutableSet }

import trees._
import inox._
/**
 * A context-insensitive, field-sensitive control-flow analysis that computes
 * the closures that are passed to call backs of given function.
 */
class CICFA(val program: Program { val trees: Trees }, rootfunid: Identifier) {

  import program._
  import program.trees._
  import program.symbols._
  import program.trees.exprOps._

  // Abstract values and closures
  sealed abstract class AbsValue
  case class Closure(lam: Lambda) extends AbsValue
  case class External() extends AbsValue

  case class AbsEnv(store: Map[Variable, Set[AbsValue]]) { // mapping from a set of live variables to their value
    // checks if this >= AbsElem
    def greaterEquals(other: AbsEnv): Boolean = {
      other.store.forall {
        case (k, v) => store.contains(k) &&
          other.store(k).subsetOf(store(k))
      }
    }

    // checks if this > AbsElem
    /*def greater(other: AbsEnv): Boolean = {
      var foundLargerTargets = true
      val geq = other.store.forall {
        case (k, v) =>
          if (store.contains(k) && other.store(k).subsetOf(store(k))) {
            // did we find a strictly larger set?
            if (!foundLargerTargets)
              foundLargerTargets = (store(k).size > other.store(k).size)
            true
          } else false
      }
      if (geq) {
        foundLargerTargets ||
          (store.keySet.size > other.store.keySet.size) // we have more bindings than the other store
      } else false
    }*/

    def join(other: AbsEnv): AbsEnv = {
      val ikeys = store.keySet.intersect(other.store.keySet)
      val jstore = (store.keySet ++ other.store.keySet).map {
        case v if ikeys(v)                => (v -> (store(v) ++ other.store(v)))
        case v if store.contains(v)       => (v -> store(v))
        case v if other.store.contains(v) => (v -> other.store(v))
      }.toMap
      AbsEnv(jstore)
    }

    // this is a disjoint union, where only the new keys that are found are added to the map (this likely to be efficient)
    def ++(other: AbsEnv): AbsEnv = {
      AbsEnv(this.store ++ (other.store.keySet -- this.store.keySet).map { v => v -> other.store(v) }.toMap)
    }

    def +(entry: (Variable, Set[AbsValue])): AbsEnv = {
      AbsEnv(store + entry)
    }

    override def toString = {
      store.map{ case (k,v) => k + "-->" + v }.mkString("\n")
    }
  }

  val emptyEnv = AbsEnv(Map())

  /**
   * A helper function for combining multiple abstract values
   */
  def flatten(envs: Seq[AbsEnv]): AbsEnv = {
    AbsEnv(envs.flatMap(_.store).toMap)
  }

  case class Summary(in: AbsEnv, out: AbsEnv, ret: Set[AbsValue])

  val tabulation = MutableMap[Identifier, Summary]() // summary of each function
  val functions = program.symbols.functions

  // initialize summaries to identity function from bot to empty
  // for the root function initialize it to External
  functions.foreach {
    case (id, fd) if id != rootfunid =>
      val bot = AbsEnv(fd.params.map { vd => vd.toVariable -> Set[AbsValue]() }.toMap)
      tabulation += (id -> Summary(bot, emptyEnv, Set()))

    case (_, fd) =>
      val init = AbsEnv(fd.params.map { vd => vd.toVariable -> Set[AbsValue](External()) }.toMap)
      tabulation += (rootfunid -> Summary(init, emptyEnv, Set()))
  }

  // initialize callers to empty set
  val callers = functions.map { case (id, fd) => (id -> MutableSet[Identifier]()) }.toMap

  var escapingVars = Set[Variable]()

  var worklist = List(rootfunid)

  // iteratively process functions from the worklist.
  // (a) at every direct function call, join the arguments passed in with the `in` fact in the summary
  //       -- if the join results in a greater value, add the function back to the worklist
  // (b) use the summary in the tabulation to complete the intra-procedural analysis
  // (c) Update the caller information on seeing a function call.
  // (d) if the return value of the function is found to be different from the return value in the tabulation
  //       -- update the entry in the tabulation to a the new value
  //       -- add all callers of the function to the worklist
  // Repeat this until a fix point is reached

  // the order of traversal is very important here, so using a custom traversal
  def analyzeExpr(e: Expr, in: AbsEnv)(implicit currFunId: Identifier): (Set[AbsValue], AbsEnv) = {
    //println("Considering Expr: "+e)
    val res : (Set[AbsValue], AbsEnv) = e match {
      case Let(vd, v, body) =>
        val (res, escenv) = analyzeExpr(v, in)
        val (bres, bescenv) = analyzeExpr(body, AbsEnv(in.store + (vd.toVariable -> res)))
        (bres, escenv ++ bescenv)

      case Application(callee, args) =>

        val (targets, escenv) = analyzeExpr(callee, in)
        val absres = args.map(analyzeExpr(_, in))
        val absargs = absres.map(_._1)
        val argescenv = flatten(absres.map(_._2))

        val resabs = targets.map {
          case Closure(lam) =>
            // create a new store with mapping for arguments and escaping variables
            val argstore = (lam.args zip absargs).map { case (vd, absval) => vd.toVariable -> absval }.toMap ++
              (in.store.filter { case (k, v) => escapingVars(k) } ++ escenv.store ++ argescenv.store)
            val (bres, besc) = analyzeExpr(lam.body, AbsEnv(argstore))
            (bres, besc)
          case _ =>
            // record all lambdas passed to external calls
            recordPassedLambdas(absargs.flatten[AbsValue].toSet, in)
            // invoking an external lambda will result in another external lambda
            (Set(External()), emptyEnv)
        }
        val resval = resabs.foldLeft(Set[AbsValue]()) {
          case (acc, (resvals, _)) => acc ++ resvals
        }
        val resesc = argescenv ++ flatten(resabs.map(_._2).toSeq)
        (resval, resesc)

      case lam @ Lambda(args, body) =>
        // create a new Closure
        val capvars = variablesOf(lam)
        escapingVars ++= capvars // make all captured variables as escaping
        (Set(Closure(lam)), AbsEnv(in.store.filter(x => capvars(x._1)))) // construct an escaping environment

      case FunctionInvocation(caleeid, tps, args) =>
        // update the callers info
        callers(caleeid) += currFunId
        //(a) join the arguments passed in with the `in` fact in the summary. If the join results in a greater value, add the function back to the worklist
        val absres = args.map(analyzeExpr(_, in))
        val absargs = absres.map(_._1)
        val argesc = flatten(absres.map(_._2))
        val newenv = in ++ argesc
        val argstore = newenv.store.filter { case (k, _) => escapingVars(k) } ++ (functions(caleeid).params zip absargs).map { case (vd, absvals) => vd.toVariable -> absvals }.toMap
        val argenv = AbsEnv(argstore)

        val currSummary = tabulation(caleeid)
        if (!currSummary.in.greaterEquals(argenv)) {
          val join = currSummary.in.join(argenv)
          // here the input state has changed, so we need to reanalyze the callee (if it is not already scheduled to be analyzed
          if(!worklist.contains(caleeid))
            worklist :+= caleeid
          // update the in fact of the summary
          tabulation.update(caleeid, Summary(join, currSummary.out, currSummary.ret))
        }
        // use the out fact as a temporary result
        val outesc = currSummary.out
        (currSummary.ret, argesc ++ currSummary.out)

      case IfExpr(cond, th, el) =>
        val (_, condesc) = analyzeExpr(cond, in)
        val ifres = Seq(th, el).map(ie => analyzeExpr(ie, in))
        val absval = ifres(0)._1 ++ ifres(1)._1 // join the results of then and else branches
        val esc = condesc ++ ifres(0)._2 ++ ifres(1)._2 // join the escape sets
        (absval, esc)

      case v : Variable => (in.store.getOrElse(v, Set()), emptyEnv)

      case Ensuring(body, Lambda(Seq(resvd), pred)) =>
        val (resb, escb) = analyzeExpr(body, in)
        // this will record some calls made via contracts
        analyzeExpr(pred, in + (resvd.toVariable -> resb)) // we can ignore its result value and escaping set as it cannot be used
        (resb, escb)

      case Require(pred: Expr, body: Expr) =>
        analyzeExpr(pred, in)
        analyzeExpr(body, in)

      case NoTree(_) => (Set(), emptyEnv)

      case Operator(args, op) =>
        // every other operator will just add more esc sets and its return values cannot contain closures
        val absres = args.map(analyzeExpr(_, in))
        (Set(), flatten(absres.map(_._2)))

      //case Tuple(
      // TOOD: need to handle data types, tuples, tupleselects, match case sets and maps
    }
    //println(s"Result of $e: ${res._1.mkString(",") } and ${res._2}")
    res
  }

  var externallyEscapingLambdas = Set[Lambda]()

  def recordPassedLambdas(args: Set[AbsValue], env: AbsEnv) {
    externallyEscapingLambdas ++= passedLambdas(args, env)
  }

  def passedLambdas(vals: Set[AbsValue], env: AbsEnv): Set[Lambda] = {
    vals.flatMap {
      case Closure(lam) =>
        variablesOf(lam).flatMap { v => passedLambdas(env.store(v), env) }.toSet + lam
      case _ => Set[Lambda]()
    }
  }

  def analyze() = {
    while (!worklist.isEmpty) {
      var currfunid = worklist.head
      worklist = worklist.tail

      val oldSummary = tabulation(currfunid)
      println(s"Analyzing: $currfunid under ${oldSummary.in}")

      val (newret, newesc) = analyzeExpr(functions(currfunid).fullBody, oldSummary.in)(currfunid)

      // if the return value of the function is found to be different from the return value in the tabulation: (a) update the entry in the tabulation to a the new value (b) add all callers of the function to the worklist
      if (!newret.subsetOf(oldSummary.ret) || !oldSummary.out.greaterEquals(newesc)) {
        // update summary
        tabulation.update(currfunid, Summary(oldSummary.in, newesc, newret))
        // reanalyze all clients with the new summary
        val newcallers = callers(currfunid).filterNot(worklist.contains)
        worklist ++= newcallers
      }
    }
    println("Externally Escaping Lambdas: "+externallyEscapingLambdas.mkString("\n"))
  }
}
