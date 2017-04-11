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
trait CICFA {

  val program: Program { val trees: Trees }
  val rootfunid: Identifier

  import program._
  import program.trees._
  import program.symbols._
  import program.trees.exprOps._

  // Abstract values and closures
  sealed abstract class AbsValue
  case class Closure(lam: Lambda) extends AbsValue
  sealed abstract class AbsObj extends AbsValue {
    val argvars: Seq[Variable]
  }
  case class ConsObject(adt: ADT, argvars: Seq[Variable]) extends AbsObj // the argvars in the object are more like addresses and may not correspond to variables in the program (they are considered escaping)
  case class TupleObject(tp: Tuple, argvars: Seq[Variable]) extends AbsObj
  case class External() extends AbsValue

  case class AbsEnv(store: Map[Variable, Set[AbsValue]]) { // mapping from a set of live variables to their value
    // checks if this >= AbsElem
    def greaterEquals(other: AbsEnv): Boolean = {
      other.store.forall {
        case (k, v) => store.contains(k) &&
          other.store(k).subsetOf(store(k))
      }
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

    // this is a disjoint union, where only the new keys that are found are added to the map (this likely to be efficient)
    def ++(other: AbsEnv): AbsEnv = {
      AbsEnv(this.store ++ (other.store.keySet -- this.store.keySet).map { v => v -> other.store(v) }.toMap)
    }

    def +(entry: (Variable, Set[AbsValue])): AbsEnv = {
      AbsEnv(store + entry)
    }

    override def toString = {
      store.map { case (k, v) => k + "-->" + v }.mkString("\n")
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

  // a mapping from ADTs to argvars (used to represent arguments of each ADT creation by a fresh variable)
  var objectsMap = Map[Expr, AbsObj]()
  def getOrCreateObject(objExpr: Expr): AbsObj = {
    if (objectsMap.contains(objExpr))
      objectsMap(objExpr)
    else {
      objExpr match {
        case adt: ADT =>
          val argvars = freshVars(adt.args.size) // represent each arg by a fresh variable
          val obj = ConsObject(adt, argvars)
          objectsMap += (adt -> obj)
          obj

        case tp: Tuple =>
          val obj = TupleObject(tp, freshVars(tp.exprs.size))
          objectsMap += (tp -> obj)
          obj
      }
    }
  }

  var creatorMap = Map[Lambda, MutableSet[Identifier]]()  // functions creating Lambdas
  def addOrUpdateCreator(l: Lambda, id: Identifier) =
    if(creatorMap.contains(l))
      creatorMap(l) += id
    else creatorMap += (l -> MutableSet(id))

  var appliedLambdas = Set[Lambda]()       // set of lambdas that are applied
  var externallyEscapingLambdas = Set[Lambda]() // set of lambdas that are passed to an call back (so in principle like applied lambdas in the absence of information about the caller)

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

  def freshVars(size: Int) = {
    (1 to size).map { i => Variable(FreshIdentifier("arg" + i, true), Untyped, immutable.Set[Flag]()) }.toSeq
  }

  // iteratively process functions from the worklist.
  // (a) at every direct function call, join the arguments passed in with the `in` fact in the summary
  //       -- if the join results in a greater value, add the function back to the worklist
  // (b) use the summary in the tabulation to complete the intra-procedural analysis
  // (c) Update the caller information on seeing a function call.
  // (d) if the return value of the function is found to be different from the return value in the tabulation
  //       -- update the entry in the tabulation to a the new value
  //       -- add all callers of the function to the worklist
  // Repeat this until a fix point is reached

  lazy val functions = program.symbols.functions
  // initialize callers to empty set
  lazy val callers = functions.map { case (id, fd) => (id -> MutableSet[Identifier]()) }.toMap

  var escapingVars = Set[Variable]()

  var worklist = List[Identifier]()

  // the order of traversal is very important here, so using a custom traversal
  def analyzeExpr(e: Expr, in: AbsEnv)(implicit currFunId: Identifier): (Set[AbsValue], AbsEnv) = {
    //println("Considering Expr: " + e)
    val res: (Set[AbsValue], AbsEnv) = e match {
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
            // record that the lambda is applied
            appliedLambdas += lam
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
        // record the creator of the Lambda
        addOrUpdateCreator(lam, currFunId)
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
        val argstore = newenv.store.filter { case (k, _) => escapingVars(k) } ++ (getFunction(caleeid).params zip absargs).map { case (vd, absvals) => vd.toVariable -> absvals }.toMap
        val argenv = AbsEnv(argstore)

        val currSummary = tabulation(caleeid)
        if (!currSummary.in.greaterEquals(argenv)) {
          val join = currSummary.in.join(argenv)
          // here the input state has changed, so we need to reanalyze the callee (if it is not already scheduled to be analyzed
          if (!worklist.contains(caleeid))
            worklist :+= caleeid
          // update the in fact of the summary
          tabulation.update(caleeid, Summary(join, currSummary.out, currSummary.ret))
        }
        // use the out fact as a temporary result
        val outesc = currSummary.out
        (currSummary.ret, argesc ++ currSummary.out)

      case adt @ ADT(adttype, args) =>
        val absres = args.map(analyzeExpr(_, in))
        val absargs = absres.map(_._1)
        val argesc = flatten(absres.map(_._2))
        // create a new object
        val obj = getOrCreateObject(adt)
        escapingVars ++= obj.argvars // make all argument variables escaping as they represent addresses that could be live across functions
        val esc = (obj.argvars zip absargs).toMap ++ argesc.store // construct an escaping environment
        (Set(obj), AbsEnv(esc))

      case sel @ ADTSelector(adtExpr, selector) =>
        val (absAdts, esc) = analyzeExpr(adtExpr, in)
        val resvals = absAdts.flatMap {
          case ConsObject(cons, argvars) =>
            val selarg = argvars(sel.selectorIndex)
            in.store.getOrElse(selarg, Set[AbsValue]())

          case External() => // here, we are dereferencing an external ADT and hence should be external
            Set[AbsValue](External())

          case _ => Set[AbsValue]() // these are type incompatible entries
        }
        (resvals, esc)

      case tp @ Tuple(args) =>
        val absres = args.map(analyzeExpr(_, in))
        val absargs = absres.map(_._1)
        val argesc = flatten(absres.map(_._2))
        // create a new object
        val obj = getOrCreateObject(tp)
        escapingVars ++= obj.argvars // make all argument variables escaping as they represent addresses that could be live across functions
        val esc = (obj.argvars zip absargs).toMap ++ argesc.store // construct an escaping environment
        (Set(obj), AbsEnv(esc))

      case TupleSelect(tp, index) =>
        val (absTups, esc) = analyzeExpr(tp, in)
        val resvals = absTups.flatMap {
          case TupleObject(_, argvars) =>
            val selarg = argvars(index)
            in.store.getOrElse(selarg, Set[AbsValue]())

          case External() => // here, we are dereferencing an external Tuple and hence should be external
            Set[AbsValue](External())

          case _ => Set[AbsValue]() // these are type incompatible entries
        }
        (resvals, esc)

      case IfExpr(cond, th, el) =>
        val (_, condesc) = analyzeExpr(cond, in)
        val ifres = Seq(th, el).map(ie => analyzeExpr(ie, in))
        val absval = ifres(0)._1 ++ ifres(1)._1 // join the results of then and else branches
        val esc = condesc ++ ifres(0)._2 ++ ifres(1)._2 // join the escape sets
        (absval, esc)

      case MatchExpr(scr, cases) =>
        val (absscr, scresc) = analyzeExpr(scr, in)
        val casesres = cases.map {
          case MatchCase(pat, gud, body) =>
            val patEnv = in ++ patternBindings(absscr, pat, in)
            // get esc set of gud
            val (_, gdesc) = gud.map(analyzeExpr(_, patEnv)).getOrElse((Set(), emptyEnv))
            // analyze the body
            val (bvals, besc) = analyzeExpr(body, patEnv)
            (bvals, gdesc ++ besc)
        }
        (casesres.flatMap(_._1).toSet, flatten(casesres.map(_._2)) ++ scresc)

      case v: Variable => (in.store.getOrElse(v, Set()), emptyEnv)

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
      // TODO: need to handle sets and maps
    }
    //println(s"Result of $e: ${res._1.mkString(",")} and ${res._2}")
    res
  }

  /**
   * Returns an environment in which pattern variables are bounded correctly to their abstract values
   */
  def patternBindings(scr: Set[AbsValue], pat: Pattern, env: AbsEnv): AbsEnv = {
    pat match {
      case InstanceOfPattern(Some(binder), _) => AbsEnv(Map(binder.toVariable -> scr))
      case WildcardPattern(Some(binder))      => AbsEnv(Map(binder.toVariable -> scr))
      case ADTPattern(binderOpt, _, subPats) =>
        val patstore = scr.flatMap {
          case ConsObject(_, argvars) =>
            (subPats zip argvars).flatMap {
              case (subpat, arg) =>
                patternBindings(env.store.getOrElse(arg, Set[AbsValue]()), subpat, env).store
            }
          case ext @ External() =>
            subPats.flatMap { subpat => patternBindings(Set(ext), subpat, env).store }
          case _ => Map[Variable, Set[AbsValue]]() // ignore these cases
        }.toMap
        // add the binding corresponding to binderOpt
        val resenv = AbsEnv(binderOpt.map(vd => patstore + (vd.toVariable -> scr)).getOrElse(patstore))
        //println("Binding after ADT pattern: "+resenv)
        resenv
      case _ => emptyEnv // no binding can be constructed in these cases
      // TODO handle Tuple patterns
    }

  }

  def analyze() = {
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
    worklist = List(rootfunid)

    while (!worklist.isEmpty) {
      var currfunid = worklist.head
      worklist = worklist.tail

      val oldSummary = tabulation(currfunid)
      //println(s"Analyzing: $currfunid under ${oldSummary.in}")

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
    //println("Externally Escaping Lambdas: " + externallyEscapingLambdas.mkString("\n"))
  }

  /**
   * Information for the client
   */
  val locallyAppliedLambdas = appliedLambdas
  val externallyInvokableLambdas = externallyEscapingLambdas

  def creators(l: Lambda) = creatorMap(l).toSet
}
