/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package termination

import scala.collection.mutable.{Map => MutableMap, Set => MutableSet, ListBuffer}

import trees._
import inox._

/** A context-insensitive, field-sensitive control-flow analysis that computes
  * the closures that are passed to call backs of given function.
  */
trait CICFA {

  val program: Program { val trees: Trees }

  import program._
  import program.trees._
  import program.symbols._
  import program.trees.exprOps._

  sealed abstract class Function {
    def body: Expr

    override def equals(that: Any): Boolean = (this, that) match {
      case (n1: NamedFunction, n2: NamedFunction) => n1.tfd == n2.tfd
      case (l1: LambdaFunction, l2: LambdaFunction) => l1.lambda == l2.lambda
      case _ => false
    }

    override def hashCode: Int = this match {
      case n: NamedFunction => n.tfd.hashCode
      case l: LambdaFunction => l.lambda.hashCode
    }

    override def toString: String = this match {
      case n: NamedFunction => n.tfd.id.asString
      case l: LambdaFunction => l.lambda.asString
    }
  }

  implicit class NamedFunction(val tfd: TypedFunDef) extends Function {
    def body: Expr = tfd.fullBody
  }

  implicit class LambdaFunction(val lambda: Lambda) extends Function {
    def body: Expr = lambda.body
  }

  // Abstract values and closures
  sealed abstract class AbsValue
  case class Closure(lam: Lambda) extends AbsValue
  sealed abstract class AbsObj extends AbsValue {
    val argvars: Seq[Variable]
  }
  // the argvars in the object are more like addresses and may not
  // correspond to variables in the program (they are considered escaping)
  case class ConsObject(adt: ADT, argvars: Seq[Variable]) extends AbsObj
  case class TupleObject(tp: Tuple, argvars: Seq[Variable]) extends AbsObj
  case object External extends AbsValue

  // mapping from a set of live variables to their value
  case class AbsEnv(store: Map[Variable, Set[AbsValue]]) {
    // checks if this >= AbsElem
    def greaterEquals(other: AbsEnv): Boolean = other.store.forall {
      case (k, v) => store.contains(k) && other.store(k).subsetOf(store(k))
    }

    def join(other: AbsEnv): AbsEnv = {
      val ikeys = store.keySet.intersect(other.store.keySet)
      val jstore = (store.keySet ++ other.store.keySet).map {
        case v if ikeys(v)                => (v -> (store(v) ++ other.store(v)))
        case v if store.contains(v)       => (v -> store(v))
        case v if other.store.contains(v) => (v -> other.store(v))
      }.toMap
      AbsEnv(jstore)
    }

    // this is a disjoint union, where only the new keys that
    // are found are added to the map (this likely to be efficient)
    def ++(other: AbsEnv): AbsEnv = {
      AbsEnv(store ++ (other.store.iterator.filter(p => !(store contains p._1))))
    }

    def +(entry: (Variable, Set[AbsValue])): AbsEnv = {
      AbsEnv(store + entry)
    }

    override def toString = {
      store.map { case (k, v) => k + "-->" + v }.mkString("\n")
    }
  }

  private val emptyEnv = AbsEnv(Map())

  /** A helper function for combining multiple abstract values */
  private def flatten(envs: Seq[AbsEnv]): AbsEnv = {
    AbsEnv(envs.flatMap(_.store).toMap)
  }

  case class Summary(in: AbsEnv, out: AbsEnv, ret: Set[AbsValue])

  private val cache: MutableMap[Identifier, Analysis] = MutableMap.empty
  def analyze(id: Identifier): Analysis = cache.getOrElseUpdate(id, {
    val timer = ctx.timers.termination.cfa.start()
    val analysis = new Analysis(id)
    timer.stop()
    analysis
  })

  class Analysis(id: Identifier) {
    val tfd = getFunction(id).typed

    private[this] var failed = false

    // summary of each function
    private val tabulation: MutableMap[Function, Summary] = MutableMap.empty
    private val types: MutableMap[Identifier, Seq[Type]] = MutableMap.empty

    // initialize summaries to identity function from bot to empty
    // for the current function, initialize it to External
    private def getTabulation(fun: Function): Summary = tabulation.getOrElseUpdate(fun, {
      Summary(fun match {
        case n: NamedFunction =>
          if ((types contains n.tfd.id) && types(n.tfd.id) != n.tfd.tps) failed = true
          types(n.tfd.id) = n.tfd.tps

          if (id == n.tfd.id) AbsEnv(n.tfd.fd.params.map(vd => vd.toVariable -> Set[AbsValue](External)).toMap)
          else AbsEnv(n.tfd.params.map(vd => vd.toVariable -> Set[AbsValue]()).toMap)

        case l: LambdaFunction =>
          AbsEnv(l.lambda.args.map(vd => vd.toVariable -> Set[AbsValue]()).toMap)
      }, emptyEnv, Set())
    })

    // a mapping from ADTs to argvars (used to represent arguments of each ADT creation by a fresh variable)
    private val objectsMap: MutableMap[Expr, AbsObj] = MutableMap.empty
    private def getOrCreateObject(objExpr: Expr): AbsObj =
      objectsMap.getOrElseUpdate(objExpr, objExpr match {
        case adt: ADT => ConsObject(adt, freshVars(adt.args.size))
        case tp: Tuple => TupleObject(tp, freshVars(tp.exprs.size))
      })

    // set of lambdas that are applied
    private val appliedLambdas: MutableSet[Lambda] = MutableSet.empty

    // set of lambdas that are passed to a call back (so in principle like
    // applied lambdas in the absence of information about the caller)
    private val externallyEscapingLambdas: MutableSet[Lambda] = MutableSet.empty

    private def recordPassedLambdas(args: Set[AbsValue], env: AbsEnv): Unit = {
      externallyEscapingLambdas ++= passedLambdas(args, env)
    }

    private def passedLambdas(vals: Set[AbsValue], env: AbsEnv): Set[Lambda] = vals.flatMap {
      case Closure(lam) => variablesOf(lam).flatMap { v => passedLambdas(env.store(v), env) }.toSet + lam
      case _ => Set[Lambda]()
    }

    private def freshVars(size: Int) = (1 to size).map(i => Variable.fresh("arg" + i, Untyped, true)).toSeq

    // iteratively process functions from the worklist.
    // (a) at every direct function call, join the arguments passed in with the `in` fact in the summary
    //       -- if the join results in a greater value, add the function back to the worklist
    // (b) use the summary in the tabulation to complete the intra-procedural analysis
    // (c) Update the caller information on seeing a function call.
    // (d) if the return value of the function is found to be different from the return value in the tabulation
    //       -- update the entry in the tabulation to a the new value
    //       -- add all callers of the function to the worklist
    // Repeat this until a fix point is reached

    // initialize callers to empty sets
    private val callers: MutableMap[Function, MutableSet[Function]] = MutableMap.empty
    private def getCallers(fun: Function): MutableSet[Function] = callers.getOrElseUpdate(fun, MutableSet.empty)

    private val escapingVars: MutableSet[Variable] = MutableSet.empty

    val worklist = new ListBuffer[Function]()
    worklist += tfd

    // the order of traversal is very important here, so using a custom traversal
    private def rec(e: Expr, in: AbsEnv)(implicit current: Function): (Set[AbsValue], AbsEnv) = {
      //println("Considering Expr: " + e)
      val res: (Set[AbsValue], AbsEnv) = e match {
        case Let(vd, v, body) =>
          val (res, escenv) = rec(v, in)
          val (bres, bescenv) = rec(body, AbsEnv(in.store + (vd.toVariable -> res)))
          (bres, escenv ++ bescenv)

        case Application(callee, args) =>
          val (targets, escenv) = rec(callee, in)
          val absres = args.map(rec(_, in))
          val absargs = absres.map(_._1)
          val argescenv = flatten(absres.map(_._2))

          val resabs = targets.map {
            case Closure(lam) =>
              getCallers(lam) += current

              // record that the lambda is applied
              appliedLambdas += lam

              // create a new store with mapping for arguments and escaping variables
              val argstore = in.store.filterKeys(escapingVars) ++
                (lam.args.map(_.toVariable) zip absargs) ++
                escenv.store ++
                argescenv.store
              val argenv = AbsEnv(argstore)

              val currSummary = getTabulation(lam)
              if (!currSummary.in.greaterEquals(argenv)) {
                val join = currSummary.in.join(argenv)
                // here the input state has changed, so we need to reanalyze the callee
                // (if it is not already scheduled to be analyzed)
                if (!worklist.contains(lam))
                  worklist += lam
                // update the in fact of the summary
                tabulation.update(lam, Summary(join, currSummary.out, currSummary.ret))
              }

              // use the out fact as a temporary result
              (currSummary.ret, currSummary.out)
            case _ =>
              // record all lambdas passed to external calls
              recordPassedLambdas(absargs.flatten[AbsValue].toSet, in)
              // invoking an external lambda will result in another external lambda
              (Set(External), emptyEnv)
          }
          val resval = resabs.foldLeft(Set[AbsValue]()) { case (acc, (resvals, _)) => acc ++ resvals }
          val resesc = argescenv ++ flatten(resabs.map(_._2).toSeq)
          (resval, resesc)

        case lam @ Lambda(args, body) =>
          val capvars = variablesOf(lam)
          escapingVars ++= capvars // make all captured variables as escaping
          val currSummary = getTabulation(lam)
          val capenv = AbsEnv(in.store.filterKeys(capvars))
          if (!currSummary.in.greaterEquals(capenv)) {
            val join = currSummary.in.join(capenv)
            tabulation.update(lam, Summary(join, currSummary.out, currSummary.ret))
          }
          (Set(Closure(lam)), AbsEnv(in.store.filterKeys(capvars)))

        case fi @ FunctionInvocation(_, _, args) =>
          val tfd = fi.tfd
          // update the callers info
          getCallers(tfd) += current
          // (a) join the arguments passed in with the `in` fact in the summary.
          //     If the join results in a greater value, add the function back to the worklist.
          val absres = args.map(rec(_, in))
          val absargs = absres.map(_._1)
          val argesc = flatten(absres.map(_._2))
          val newenv = in ++ argesc
          val argstore = newenv.store.filterKeys(escapingVars) ++
            (tfd.params.map(_.toVariable) zip absargs)
          val argenv = AbsEnv(argstore)

          val currSummary = getTabulation(tfd)
          if (!currSummary.in.greaterEquals(argenv)) {
            val join = currSummary.in.join(argenv)
            // here the input state has changed, so we need to reanalyze the callee
            // (if it is not already scheduled to be analyzed)
            if (!worklist.contains(tfd))
              worklist += tfd
            // update the in fact of the summary
            tabulation.update(tfd, Summary(join, currSummary.out, currSummary.ret))
          }
          // use the out fact as a temporary result
          (currSummary.ret, argesc ++ currSummary.out)

        case adt @ ADT(adttype, args) =>
          val absres = args.map(rec(_, in))
          val absargs = absres.map(_._1)
          val argesc = flatten(absres.map(_._2))
          // create a new object
          val obj = getOrCreateObject(adt)
          // make all argument variables escaping as they represent addresses that could be live across functions
          escapingVars ++= obj.argvars
          // construct an escaping environment
          val esc = (obj.argvars zip absargs).toMap ++ argesc.store
          (Set(obj), AbsEnv(esc))

        case sel @ ADTSelector(adtExpr, selector) =>
          val (absAdts, esc) = rec(adtExpr, in)
          val resvals: Set[AbsValue] = absAdts.flatMap {
            case ConsObject(cons, argvars) =>
              val selarg = argvars(sel.selectorIndex)
              in.store.getOrElse(selarg, Set())

            // here, we are dereferencing an external ADT and hence should be external
            case External => Set(External: AbsValue)

            // these are type incompatible entries
            case _ => Set[AbsValue]()
          }
          (resvals, esc)

        case tp @ Tuple(args) =>
          val absres = args.map(rec(_, in))
          val absargs = absres.map(_._1)
          val argesc = flatten(absres.map(_._2))
          // create a new object
          val obj = getOrCreateObject(tp)
          // make all argument variables escaping as they represent addresses that could be live across functions
          escapingVars ++= obj.argvars
          // construct an escaping environment
          val esc = (obj.argvars zip absargs).toMap ++ argesc.store
          (Set(obj), AbsEnv(esc))

        case TupleSelect(tp, index) =>
          val (absTups, esc) = rec(tp, in)
          val resvals: Set[AbsValue] = absTups.flatMap {
            case TupleObject(_, argvars) =>
              val selarg = argvars(index - 1)
              in.store.getOrElse(selarg, Set())

            // here, we are dereferencing an external Tuple and hence should be external
            case External => Set(External: AbsValue)

            // these are type incompatible entries
            case _ => Set[AbsValue]()
          }
          (resvals, esc)

        case IfExpr(cond, th, el) =>
          val (_, condesc) = rec(cond, in)
          val Seq((tval, tesc), (eval, eesc)) = Seq(th, el).map(ie => rec(ie, in))
          (tval ++ eval, condesc ++ tesc ++ eesc)

        case MatchExpr(scrut, cases) =>
          var resenv: AbsEnv = emptyEnv
          val absres = for (cse <- cases) yield {
            val patCond = conditionForPattern[Path](scrut, cse.pattern, includeBinders = true)
            val realCond = patCond withConds cse.optGuard.toSeq
            val rhsIn = realCond.elements.foldLeft(in) {
              case (in, Left((vd, e))) =>
                val (res, resc) = rec(e, in)
                resenv ++= resc
                AbsEnv(in.store + (vd.toVariable -> res))
              case (in, Right(cond)) =>
                val (res, resc) = rec(cond, in)
                resenv ++= resc
                in
            }
            rec(cse.rhs, rhsIn)
          }
          (absres.flatMap(_._1).toSet, resenv ++ flatten(absres.map(_._2)))

        case v: Variable => (in.store.getOrElse(v, Set()), emptyEnv)

        case Ensuring(body, Lambda(Seq(resvd), pred)) =>
          val (resb, escb) = rec(body, in)
          // this will record some calls made via contracts
          // we can ignore its result value and escaping set as it cannot be used
          rec(pred, in + (resvd.toVariable -> resb))
          (resb, escb)

        case Require(pred, body) =>
          // pred cannot have an escaping set
          rec(pred, in)
          rec(body, in)

        case Assert(pred, _, body) =>
          // pred cannot have an escaping set
          rec(pred, in)
          rec(body, in)

        case NoTree(_) => (Set(), emptyEnv)

        case Operator(args, op) =>
          // every other operator will just add more esc sets and its return values cannot contain closures
          val absres = args.map(rec(_, in))
          (Set(), flatten(absres.map(_._2)))
        // TODO: need to handle sets and maps
      }

      //println(s"Result of $e: ${res._1.mkString(",")} and ${res._2}")
      res
    }

    while (!worklist.isEmpty && !failed) {
      var fun = worklist.remove(0)
      val oldSummary = getTabulation(fun)
      //println(s"Analyzing: $currfunid under ${oldSummary.in}")

      val (newret, newesc) = rec(fun.body, oldSummary.in)(fun)

      // if the return value of the function is found to be different from the return value in the tabulation:
      // (a) update the entry in the tabulation to a the new value
      // (b) add all callers of the function to the worklist
      if (!newret.subsetOf(oldSummary.ret) || !oldSummary.out.greaterEquals(newesc)) {
        // update summary
        tabulation.update(fun, Summary(oldSummary.in, newesc, newret))
        // reanalyze all clients with the new summary
        val newcallers = getCallers(fun).filterNot(worklist.contains)
        worklist ++= newcallers

        if (fun == (tfd: Function)) {
          def escapingLambdas(rets: Set[AbsValue], seen: Set[AbsValue]): Set[Function] = (rets -- seen).flatMap {
            case Closure(lam) => Set(lam: Function)
            case co @ ConsObject(_, vars) =>
              escapingLambdas(vars.flatMap(v => newesc.store.getOrElse(v, Set.empty)).toSet, seen + co)
            case to @ TupleObject(_, vars) =>
              escapingLambdas(vars.flatMap(v => newesc.store.getOrElse(v, Set.empty)).toSet, seen + to)
            case _ => Set.empty[Function]
          }

          worklist ++= escapingLambdas(newret, Set.empty).filterNot(worklist.contains)
        }
      }
    }

    private val allEscaping: Set[Lambda] = externallyEscapingLambdas.toSet.flatMap { l: Lambda =>
      var llams = Set(l)
      var callees = Set[Identifier]()

      exprOps.postTraversal {
        case nl: Lambda => llams += nl
        case FunctionInvocation(id, _, _) => callees += id
        case _ =>
      } (l.body)

      callees.foreach { cid =>
        val fd = getFunction(cid)
        (transitiveCallees(fd) + fd).foreach { tc =>
          exprOps.postTraversal {
            case nl: Lambda => llams += nl
            case _ =>
          } (tc.fullBody)
        }
      }

      llams
    }

    def isApplied(l: Lambda): Boolean = failed || appliedLambdas(l) || allEscaping(l)
  }
}
