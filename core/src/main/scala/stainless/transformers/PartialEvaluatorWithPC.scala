/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package transformers

import scala.language.existentials
import scala.concurrent.duration._
import scala.collection.mutable.{Map => MutableMap}
import scala.util.DynamicVariable

import inox.{Context, Semantics}
import inox.utils._
import inox.solvers._
import inox.solvers.SolverResponses._
import inox.evaluators.EvaluationResults

import stainless.transformers._

object DebugSectionPartialEval extends inox.DebugSection("partial-eval")

case class PartialEvalError(msg: String) extends Exception(msg)

trait PartialEvaluatorWithPC extends TransformerWithPC { self =>
  implicit val context: inox.Context
  protected val semantics: inox.SemanticsProvider { val trees: self.trees.type }

  private[this] lazy val program = inox.Program(trees)(symbols)
  private[this] lazy val programSemantics = semantics.getSemantics(program)
  private[this] lazy val solver = programSemantics.getSolver(context).withTimeout(150.millis).toAPI
  private[this] lazy val groundEvaluator = programSemantics.getEvaluator(context)

  import trees._
  import symbols.{simplifier => _, _}
  import exprOps._
  import dsl._

  import context.reporter

  type Env = Path

  override implicit def pp = Path

  private lazy val simplifier = symbols.simplifier(inox.solvers.PurityOptions.assumeChecked)

  private var doNotUnfold: Set[Identifier] = Set.empty
  private def canUnfold(id: Identifier): Boolean = !doNotUnfold.contains(id)

  final private[this] implicit class PathOps(val path: Path) {
    def contains(cond: Expr): Boolean = {
      if (cond.getType != BooleanType()) {
        reporter.error(s"$cond should have type Boolean, found: ${cond.getType})")
        reporter.error(explainTyping(cond)(PrinterOptions(printUniqueIds = false, symbols = Some(symbols))))
        assert(cond.getType == BooleanType())
      }

      simplifier.transform(path implies cond) match {
        case BooleanLiteral(res) => res
        case res => solver.solveVALID(res).getOrElse(false)
      }
    }
  }

  private[this] implicit val debugSection = DebugSectionPartialEval

  private[this] val maxUnfoldingSteps: Int = 50
  private[this] var unfoldingStepsLeft: Map[Identifier, Int] = Map().withDefault(_ => maxUnfoldingSteps)

  override def initEnv: Path = Path.empty

  private val cache = new LruCache[Expr, (Path, Expr)](1000)

  override protected def rec(expr: Expr, path: Path): Expr = {
    if (context.interruptManager.isInterrupted) {
      return expr
    }

    val cached = cache.get(expr).filter(_._1 == path).map(_._2)
    if (cached.isDefined) {
      return cached.get
    }

    val res = expr match {
      case b: BooleanLiteral => b
      case c: Choose => c

      case Require(pred, body) => rec(pred, path) match {
        case BooleanLiteral(true) =>
          rec(body, path withCond pred)
        case BooleanLiteral(false) =>
          Require(BooleanLiteral(false), body)
        case rp =>
          Require(rp, rec(body, path withCond pred))
      }

      case Assert(pred, error, body) => rec(pred, path) match {
        case BooleanLiteral(true) => rec(body, path withCond pred)
        case BooleanLiteral(false) => Assert(pred, error, body)
        case rp => rec(body, path withCond pred)
      }

      case Assume(pred, body) => rec(pred, path) match {
        case BooleanLiteral(true) => rec(body, path withCond pred)
        case BooleanLiteral(false) => Assume(pred, body)
        case rp => rec(body, path withCond pred)
      }

      case Ensuring(body, pred) =>
        rec(Ensuring(body, pred).toAssert, path)

      case Annotated(body, flags) =>
        rec(body, path)

      case Let(vd, v, b) =>
        rec(replaceFromSymbols(Map(vd -> rec(v, path)), b), path)

      case m @ MatchExpr(scrut, cases) =>
        reduceMatch(m, path)

      case fi @ FunctionInvocation(id, tps, args) if canUnfold(fi.id) && !fi.tfd.fd.flags.contains("extern") =>
        val rargs = args.map(rec(_, path))

        unfold(fi, rargs, path) match {
          case Some(unfolded) => rec(unfolded, path)
          case None => FunctionInvocation(id, tps, rargs)
        }

      case Application(e, es) => rec(e, path) match {
        case l: Lambda =>
          val res = es.map(rec(_, path))
          rec(l.withParamSubst(res, l.body), path)

        case Assume(pred, l: Lambda) =>
          val res = es.map(rec(_, path))
          rec(assume(pred, application(l, res)), path)

        case re =>
          application(re, es.map(rec(_, path)))
      }

      // FIXME: Reduce under lambda or not?
      case Lambda(args, body) =>
        Lambda(args, body)

      case Implies(l, r) => rec(l, path) match {
        case BooleanLiteral(false) => BooleanLiteral(true)
        case le => rec(or(not(le), r), path)
      }

      case And(e +: es) => rec(e, path) match {
        case BooleanLiteral(true) => rec(andJoin(es), path withCond e)
        case BooleanLiteral(false) => BooleanLiteral(false)
        case re =>
          val res = rec(andJoin(es), path withCond re)
          if (res == BooleanLiteral(false)) BooleanLiteral(false)
          else and(re, res)
      }

      case Or(e +: es) => rec(e, path) match {
        case BooleanLiteral(true) => BooleanLiteral(true)
        case BooleanLiteral(false) => rec(orJoin(es), path)
        case re =>
          val res = rec(orJoin(es), path withCond not(re))
          if (res == BooleanLiteral(true)) {
            BooleanLiteral(true)
          } else {
            or(re, res)
          }
      }

      case IfExpr(c, t, e) => rec(c, path) match {
        case BooleanLiteral(true) => rec(t, path withCond c)
        case BooleanLiteral(false) => rec(e, path withCond not(c))
        case rc =>
          val rt = rec(t, path withCond rc)
          val re = rec(e, path withCond not(rc))
          if (rt == re) {
            rt
          } else {
            ifExpr(rc, rt, re)
          }
      }

      case IsConstructor(ADT(id1, _, _), id2) =>
        BooleanLiteral(id1 == id2)

      case IsConstructor(e, id) =>
        val re = rec(e, path)
        isConstructor(re, id, path) match {
          case Some(b) => BooleanLiteral(b)
          case None => IsConstructor(re, id)
        }

      case s @ ADTSelector(expr, sel) => rec(expr, path) match {
        case r @ ADT(adt, _, args) =>
          rec(args(s.selectorIndex), path)

        case other =>
          adtSelector(other, sel)
      }

      case sel @ TupleSelect(t, idx) => rec(t, path) match {
        case Tuple(exprs) =>
          rec(exprs(sel.index - 1), path)

        case other =>
          TupleSelect(other, idx)
      }

      case FiniteMap(pairs, default, keyType, valueType) =>
        finiteMap(pairs.map(recPair(_, path)), rec(default, path), keyType, valueType)

      case MapApply(map, key) => (rec(map, path), rec(key, path)) match {
        case (FiniteMap(pairs, default, _, _), key) =>
          pairs.toMap.getOrElse(key, default)

        case (map, key) => MapApply(map, key)
      }

      case MapUpdated(map, key, value) => (rec(map, path), rec(key, path), rec(value, path)) match {
        case (map @ FiniteMap(pairs, default, from, to), key, value) =>
          finiteMap(pairs.toMap.updated(key, value).toSeq, default, from, to)

        case (map, key, value) => MapUpdated(map, key, value)
      }

      case BagAdd(bag, elem) => (rec(bag, path), rec(elem, path)) match {
        case (FiniteBag(els, tpe), evElem) =>
          val (matching, rest) = els.partition(_._1 == evElem)
          val mul = matching.lastOption.map {
            case (_, IntegerLiteral(i)) => IntegerLiteral(i + 1)
            case (_, e) => Plus(e, IntegerLiteral(1))
          }.getOrElse(IntegerLiteral(1))

          finiteBag(rest :+ (evElem -> mul), tpe)

        case (le, re) => BagAdd(le, re)
      }

      case MultiplicityInBag(elem, bag) => (rec(elem, path), rec(bag, path)) match {
        case (evElem, FiniteBag(els, tpe)) =>
          els.collect { case (k,v) if k == evElem => v }.lastOption.getOrElse(IntegerLiteral(0))
        case (le, re) => MultiplicityInBag(le, re)
      }

      case BagIntersection(b1, b2) => (rec(b1, path), rec(b2, path)) match {
        case (FiniteBag(els1, tpe), FiniteBag(els2, _)) =>
          val map2 = els2.toMap
          finiteBag(els1.flatMap { case (k, v) =>
            val i = (v, map2.getOrElse(k, IntegerLiteral(0))) match {
              case (IntegerLiteral(i1), IntegerLiteral(i2)) => Some(i1 min i2)
              case (le, re) => None
            }

            i.filter(_ > 0).map(i => k -> IntegerLiteral(i))
          }, tpe)

        case (le, re) => BagIntersection(le, re)
      }

      case BagUnion(b1, b2) => (rec(b1, path), rec(b2, path)) match {
        case (FiniteBag(els1, tpe), FiniteBag(els2, _)) =>
          val (map1, map2) = (els1.toMap, els2.toMap)
          finiteBag((map1.keys ++ map2.keys).toSet.map { (k: Expr) =>
            k -> ((map1.getOrElse(k, IntegerLiteral(0)), map2.getOrElse(k, IntegerLiteral(0))) match {
              case (IntegerLiteral(i1), IntegerLiteral(i2)) => IntegerLiteral(i1 + i2)
              case (le, re) => Plus(le, re)
            })
          }.toSeq, tpe)

        case (le, re) => BagUnion(le, re)
      }

      case BagDifference(b1, b2) => (rec(b1, path), rec(b2, path)) match {
        case (FiniteBag(els1, tpe), FiniteBag(els2, _)) =>
          val map2 = els2.toMap
          finiteBag(els1.flatMap { case (k, v) =>
            val i = (v, map2.getOrElse(k, IntegerLiteral(0))) match {
              case (IntegerLiteral(i1), IntegerLiteral(i2)) => Some(i1 - i2)
              case (le, re) => None
            }

            i.filter(_ > 0).map(i => k -> IntegerLiteral(i))
          }, tpe)

        case (le, re) => BagDifference(le, re)
      }

      case FiniteBag(els, base) =>
        finiteBag(els.map { case (k, v) => (rec(k, path), rec(v, path)) }, base)

      case SetAdd(s1, elem) =>
        (rec(s1, path), rec(elem, path)) match {
          case (FiniteSet(els1, tpe), evElem) => finiteSet(els1 :+ evElem, tpe)
          case (le, re) => SetAdd(le, re)
        }

      case SetUnion(s1,s2) =>
        (rec(s1, path), rec(s2, path)) match {
          case (FiniteSet(els1, tpe), FiniteSet(els2, _)) => finiteSet(els1 ++ els2, tpe)
          case (le, re) => SetUnion(le, re)
        }

      case SetIntersection(s1,s2) =>
        (rec(s1, path), rec(s2, path)) match {
          case (FiniteSet(els1, tpe), FiniteSet(els2, _)) => finiteSet(els1 intersect els2, tpe)
          case (le, re) => SetIntersection(le, re)
        }

      case SetDifference(s1, s2) =>
        (rec(s1, path), rec(s2, path)) match {
          case (FiniteSet(els1, tpe), FiniteSet(els2, _)) => finiteSet(els1.toSet -- els2, tpe)
          case (le, re) => SetDifference(le, re)
        }

      case ElementOfSet(el,s) => (rec(el, path), rec(s, path)) match {
        case (e, FiniteSet(els, _)) => BooleanLiteral(els.contains(e))
          case (le, re) => ElementOfSet(le, re)
      }

      case SubsetOf(s1, s2) => (rec(s1, path), rec(s2, path)) match {
        case (FiniteSet(els1, _),FiniteSet(els2, _)) => BooleanLiteral(els1.toSet.subsetOf(els2.toSet))
          case (le, re) => SubsetOf(le, re)
      }

      case f @ FiniteSet(els, base) =>
        finiteSet(els.map(rec(_, path)), base)

      case LargeArray(elems, default, size, base) =>
        LargeArray(elems.mapValues(rec(_, path)), rec(default, path), size, base)

      case ArraySelect(array, index) => (rec(array, path), rec(index, path)) match {
        case (FiniteArray(elems, base), Int32Literal(i)) =>
          if (i < 0 || i >= elems.size) throw PartialEvalError("Index out of bounds @" + expr.getPos)
          elems(i)
        case (LargeArray(elems, default, Int32Literal(size), _), Int32Literal(i)) =>
          if (i < 0 || i >= size) throw PartialEvalError("Index out of bounds @" + expr.getPos)
          elems.getOrElse(i, default)
        case (arr, i) =>
          ArraySelect(arr, i)
      }

      case ArrayUpdated(array, index, value) => (rec(array, path), rec(index, path), rec(value, path)) match {
        case (FiniteArray(elems, base), Int32Literal(i), v) =>
          if (i < 0 || i >= elems.size) throw PartialEvalError("Index out of bounds @" + expr.getPos)
          FiniteArray(elems.updated(i, v), base)
        case (LargeArray(elems, default, s @ Int32Literal(size), base), Int32Literal(i), v) =>
          if (i < 0 || i >= size) throw PartialEvalError("Index out of bounds @" + expr.getPos)
          LargeArray(elems + (i -> v), default, s, base)
        case (arr, i, v) =>
          ArrayUpdated(arr, i, v)
      }

      case ArrayLength(array) => rec(array, path) match {
        case FiniteArray(elems, _) => Int32Literal(elems.size)
        case LargeArray(_, _, s, _) => s
        case arr => ArrayLength(arr)
      }

      case e if e.getType == BooleanType() && path.contains(e) =>
        BooleanLiteral(true)

      case e if e.getType == BooleanType() && path.contains(not(e)) =>
        BooleanLiteral(false)

      case e => super.rec(e, path)
    }

    val simpl = simplifyGround(res)(programSemantics, context)
    cache(expr) = path -> simpl
    simpl
  }

  private def recAndCons(es: Seq[Expr], path: Path, cons: Seq[Expr] => Expr): Expr = {
    cons(es.map(rec(_, path)))
  }

  private def recPair(pair: (Expr, Expr), path: Path): (Expr, Expr) = {
    (rec(pair._1, path), rec(pair._2, path))
  }

  private def finiteSet(els: Iterable[Expr], tpe: Type): FiniteSet = {
    FiniteSet(els.toSeq.distinct.sortBy(_.toString), tpe)
  }

  private def finiteMap(els: Iterable[(Expr, Expr)], default: Expr, from: Type, to: Type): FiniteMap = {
    FiniteMap(els.toMap.toSeq.filter { case (_, value) => value != default }.sortBy(_._1.toString), default, from, to)
  }

  private def finiteBag(els: Iterable[(Expr, Expr)], tpe: Type): FiniteBag = {
    FiniteBag(els.toMap.toSeq.filter { case (_, IntegerLiteral(i)) => i > 0 case _ => false }.sortBy(_._1.toString), tpe)
  }

  private def isConstructor(e: Expr, id: Identifier, path: Path): Option[Boolean] = {
    if (path contains IsConstructor(e, id)) {
      Some(true)
    } else {
      val adt @ ADTType(_, tps) = widen(e.getType)
      val sort = adt.getSort
      val cons = getConstructor(id, tps)
      val alts = (sort.constructors.toSet - cons).map(_.id)

      if (alts exists (id => path contains IsConstructor(e, id))) {
        Some(false)
      } else if (alts forall (id => path contains Not(IsConstructor(e, id)))) {
        Some(true)
      } else {
        None
      }
    }
  }

  private def unfold(fi: FunctionInvocation, args: Seq[Expr], path: Path): Option[Expr] = {
    lazy val unfolded = exprOps.freshenLocals(fi.tfd.withParamSubst(args, fi.tfd.fullBody))

    if (unfoldingStepsLeft(fi.id) > 0 && (!isRecursive(fi.id) || isProductiveUnfolding(fi.id, unfolded, path))) {
      decreaseUnfoldingStepsLeft(fi.id)
      Some(unfolded)
    } else {
      None
    }
  }

  private def decreaseUnfoldingStepsLeft(id: Identifier): Unit = {
    val left = unfoldingStepsLeft(id)
    unfoldingStepsLeft = unfoldingStepsLeft.updated(id, left - 1)
  }

  private def preventUnfolding[A](id: Identifier)(action: => A): A = {
    val alreadyPrevented = doNotUnfold contains id
    if (!alreadyPrevented) doNotUnfold = doNotUnfold + id
    val res = action
    if (!alreadyPrevented) doNotUnfold = doNotUnfold - id
    res
  }

  private def isProductiveUnfolding(id: Identifier, expr: Expr, path: Path): Boolean = {
    def isKnown(expr: Expr): Boolean = expr match {
      case BooleanLiteral(_) => true
      case _ => false
    }

    val invocationPaths = collectWithPC(expr) {
      case (fi: FunctionInvocation, subPath) if fi.id == id || transitivelyCalls(fi.id, id) => subPath
    }

    preventUnfolding(id) {
      invocationPaths.map(p => transform(p.toClause, path)).forall(isKnown)
    }
  }

  private def reduceMatch(e: MatchExpr, path: Path): Expr = {
    val MatchExpr(scrut, cases) = e
    val rs = transform(scrut, path)
    val (_, stop, newCases) = cases.foldLeft((path, false, Seq[MatchCase]())) {
      case (p @ (_, true, _), _) => p
      case ((soFar, _, newCases), MatchCase(pattern, guard, rhs)) =>
        transform(conditionForPattern[Path](rs, pattern, includeBinders = false)(pp).fullClause, soFar) match {
          case BooleanLiteral(false) => (soFar, false, newCases)
          case rc =>
            val path = conditionForPattern[Path](rs, pattern, includeBinders = true)(pp)
            val rg = guard.map(transform(_, soFar merge path)).getOrElse(BooleanLiteral(true))
            and(rc, rg) match {
              case BooleanLiteral(false) => (soFar, false, newCases)
              case BooleanLiteral(true) =>
                // We know path withCond rg is true here but we need the binders
                val bindings = conditionForPattern[Path](rs, pattern, includeBinders = true)(pp).bindings
                val rr = bindings.foldRight(rhs) { case ((i, e), b) => Let(i, e, b) }
                (soFar, true, newCases :+ MatchCase(WildcardPattern(None).copiedFrom(pattern), None, rr))

              case _ =>
                val rr = rhs
                val newGuard = if (rg == BooleanLiteral(true)) None else Some(rg)
                (
                  soFar merge (path withCond rg).negate,
                  false,
                  newCases :+ MatchCase(pattern, newGuard, rr)
                )
            }
        }
    }

    newCases match {
      case Seq() =>
        Assert(
          BooleanLiteral(false).copiedFrom(e),
          Some("No valid case"),
          Choose(
            ValDef(FreshIdentifier("res"), e.getType, Seq.empty).copiedFrom(e),
            BooleanLiteral(true).copiedFrom(e)
          ).copiedFrom(e)
        ).copiedFrom(e)

      case Seq(MatchCase(WildcardPattern(None), None, rhs)) if stop => transform(rhs, path)
      case _ => MatchExpr(rs, newCases).copiedFrom(e)
    }
  }
}
