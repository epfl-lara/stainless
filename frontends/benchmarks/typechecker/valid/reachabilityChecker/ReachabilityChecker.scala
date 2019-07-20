/* Author: Sarah Sallinger */
import stainless.collection._
import stainless.lang._
import stainless.annotation._
import stainless.proof._

import scala.language.postfixOps

object ReachabilityChecker {

  case class State(registers: List[Boolean]) {
    override def toString: String = {
      decreases(this)
      registers match {
        case Nil() => ";"
        case Cons(x, xs) if (x) => "1" + State(xs).toString
        case Cons(x, xs) => "0" + State(xs).toString
      }
    }
  }

  case class System(transitions: List[(State, State)])

  // -------------------------------------------------------------------
  // Main functions and their correctness:
  // -------------------------------------------------------------------

  def correctTrace(s: System,
                   initial: State,
                   target: State,
                   k: BigInt): Boolean = {
    require(k >= 0)
    val res = kReachabilityCheck(List(initial), s, target, k, initial)

    res match {
      case Trace(t) => initial == t.head && t.last == target && isTrace(s, t)
      case _ => true
    }
  }.holds


  sealed abstract class Result
  case object Unknown extends Result
  case object Unreachable extends Result
  case class Trace(states: List[State]) extends Result

  def kReachabilityCheck(currentTrace: List[State],
                         s: System,
                         target: State,
                         k: BigInt,
                         initial: State): Result = {
    require(
      k >= 0 &&
      simple(currentTrace) &&
      !currentTrace.isEmpty &&
      isTrace(s, currentTrace) &&
      canTransitionSucc(s.transitions, currentTrace.last) &&
      currentTrace.head == initial
    )
    decreases((k, BigInt(0)))

    if (currentTrace.last == target)
      Trace(currentTrace)
    else if (k == 0)
      Unknown
    else {
      exploreSuccessors(successors(s.transitions, currentTrace.last),
                        currentTrace,
                        s,
                        target,
                        k - 1,
                        false,
                        initial)
    }
  } ensuring (res =>
                res match {
                  case Trace(t) =>
                    isTrace(s, t) && !t.isEmpty && t.head == initial && t.last == target && simple(t)
                  case _ => true
                })

  def exploreSuccessors(succ: List[State],
                        currentTrace: List[State],
                        s: System,
                        target: State,
                        k: BigInt,
                        unknown: Boolean,
                        initial: State): Result = {
    require(
      k >= 0 &&
      simple(currentTrace) &&
      !currentTrace.isEmpty &&
      isTrace(s, currentTrace) &&
      canTransition(s.transitions, currentTrace.last, succ) &&
      currentTrace.head == initial)
    decreases((k,succ.length))

    succ match {
      case Nil() => if (unknown) Unknown else Unreachable
      case Cons(x, xs) =>
        if (!currentTrace.contains(x) && // needed for simpleAppend
            addStateToTrace(currentTrace, s, x) &&
            simpleAppend(currentTrace, x)) {

          val res =
            kReachabilityCheck(currentTrace :+ x, s, target, k, initial)
          res match {
            case Trace(t) => res //target found
            case Unknown =>
              exploreSuccessors(xs, currentTrace, s, target, k, true, initial)
            case Unreachable =>
              exploreSuccessors(xs,
                                currentTrace,
                                s,
                                target,
                                k,
                                unknown,
                                initial)
          }
        } else
          exploreSuccessors(xs, currentTrace, s, target, k, unknown, initial)
    }
  } ensuring (res =>
                res match {
                  case Trace(t) =>
                    isTrace(s, t) && !t.isEmpty && t.head == initial && t.last == target && simple(t)
                  case _ => true
                })

  // -------------------------------------------------------------------
  // Auxiliary functions for running the reachability check and for expressing its specification
  // -------------------------------------------------------------------

  def successors(tr: List[(State, State)], s: State): List[State] = {
    decreases(tr)
    tr match {
      case Nil() => List()
      case Cons((s1, s2), trs) =>
        if (s1 == s) Cons(s2, successors(trs, s))
        else successors(trs, s)
    }
  }

  // @induct
  def successorsTransition(tr: List[(State, State)],
                           s: State,
                           st: State): Boolean = {
    require(successors(tr, s).contains(st))
    decreases(tr)

    tr match {
      case Nil() => check(tr.contains((s, st)))
      case Cons((s1, s2), trs) =>
        if (s1 == s) {
          if (s2 == st) check(tr.contains((s, st)))
          else {
            assert(successorsTransition(trs, s, st))
            check(tr.contains((s, st)))
          }
        }
        else {
          assert(successorsTransition(trs, s, st))
          check(tr.contains((s, st)))
        }
    }

    tr.contains((s, st))
  }.holds

  def canTransition(tr: List[(State, State)],
                    x: State,
                    l: List[State]): Boolean = {
    decreases(l)
    l match {
      case Nil() => true
      case Cons(y, ys) => tr.contains((x, y)) && canTransition(tr, x, ys)
    }
  }

  def canTransitionSuccHelp(tr: List[(State, State)],
                            s: State,
                            succ: List[State]): Boolean = {

    require(subset(succ, successors(tr, s)))
    decreases(succ)

    succ match {
      case Nil() => true
      case Cons(x, xs) =>
        successorsTransition(tr, s, x) && tr.contains((s, x)) && canTransitionSuccHelp(
          tr,
          s,
          xs) && canTransition(tr, s, succ)
    }
  }.holds

  def canTransitionSucc(tr: List[(State, State)], s: State): Boolean = {
    val succ = successors(tr, s)

    subsetReflexive(succ) &&
    canTransitionSuccHelp(tr, s, succ) &&
    canTransition(tr, s, succ)

  }.holds

  def subset[X](l1: List[X], l2: List[X]): Boolean = {
    decreases(l1)
    l1 match {
      case Nil() => true
      case Cons(x, xs) => l2.contains(x) && subset(xs, l2)
    }
  }

  def subsetReflexive[X](l1: List[X]): Boolean = {
    decreases(l1)
    l1 match {
      case Nil() => subset(l1, l1)
      case Cons(x, xs) =>
        l1.contains(x) && subsetReflexive(xs) && subsetExtend(xs, xs, x) && subset(
          xs,
          l1) && subset(l1, l1)
    }
  }.holds

  def subsetExtend[X](l1: List[X], l2: List[X], x: X): Boolean = {
    require(subset(l1, l2))
    decreases(l1)

    check(l1.isEmpty || subsetExtend(l1.tail, l2, x))

    subset(l1, Cons(x, l2))
  }.holds

  def addStateToTrace(t: List[State], s: System, st: State): Boolean = {
    require(isTrace(s, t) && (t.isEmpty || s.transitions.contains((t.last, st))))
    decreases(t)

    check(t.isEmpty || addStateToTrace(t.tail, s, st))

    isTrace(s, t :+ st)
  }.holds

  def noTarget(t: List[State], target: State, x: State): Boolean = {
    require(!t.contains(target))
    decreases(t)

    val l = t :+ x

    check(t.isEmpty || noTarget(t.tail, target, x))

    x == l.last && (target == x || !l.contains(target))
  }.holds


  def isTrace(s: System, t: List[State]): Boolean = {
    decreases(t)
    t match {
      case Cons(s1, Cons(s2, ts)) =>
        s.transitions.contains((s1, s2)) &&
          isTrace(s, Cons(s2, ts))
      case _ => true
    }
  }

  def inSuccessors(tr: List[(State, State)], s1: State, s2: State): Boolean = {
    require(tr.contains((s1, s2)))
    decreases(tr)

    check(tr.isEmpty || tr.head == (s1,s2) || inSuccessors(tr.tail, s1, s2))

    successors(tr, s1).contains(s2)
  }.holds

  def disjoint[X](l1: List[X], l2: List[X]): Boolean = {
    (l1 & l2).isEmpty
  }

  def simple[X](l: List[X]): Boolean = {
    decreases(l)
    l match {
      case Nil() => true
      case Cons(x, xs) => !xs.contains(x) && simple(xs)
    }
  }

  def contentContains[X](l: List[X], x: X): Boolean = {
    require(l.contains(x))

    l.content.contains(x)
  }.holds

  def completeTrace(l: List[State],
                    s: System,
                    initial: State,
                    target: State,
                    currentTrace: List[State]): Boolean = {
    require(
      simple(currentTrace) &&
      isTrace(s, l) &&
      !l.isEmpty &&
      l.last == target &&
      !currentTrace.isEmpty &&
      l.head == currentTrace.last &&
      isTrace(s, currentTrace) &&
      currentTrace.head == initial &&
      canTransitionSucc(s.transitions, currentTrace.last) &&
      disjoint(currentTrace, l.tail) &&
      simple(l)
    )
    decreases((l.length, BigInt(0)))

    val res =
      kReachabilityCheck(currentTrace, s, target, l.length - 1, initial)

    check(if (currentTrace.last == target)
       true
     else if (l.length - 1 == 0)
       false
     else {
       val succ = successors(s.transitions, currentTrace.last)

       if (inSuccessors(s.transitions, l.head, l.tail.head)) {
         completeTraceExploreSucc(l.tail,
                                  s,
                                  succ,
                                  target,
                                  false,
                                  initial,
                                  currentTrace)
       } else
         false
     })

    res match {
      case Trace(_) => true
      case _ => false
    }

  }.holds

  def completeTraceExploreSucc(l: List[State],
                               s: System,
                               succ: List[State],
                               target: State,
                               unknown: Boolean,
                               initial: State,
                               currentTrace: List[State]): Boolean = {
    require(
      simple(currentTrace) &&
      isTrace(s, l) &&
      !l.isEmpty &&
      l.last == target &&
      !currentTrace.isEmpty &&
      succ.contains(l.head) &&
      isTrace(s, currentTrace) &&
      currentTrace.head == initial &&
      canTransition(s.transitions, currentTrace.last, succ) &&
      disjoint(currentTrace, l) &&
      simple(l)
    )
    decreases((l.length, succ.length))

    val res = exploreSuccessors(succ,
                                currentTrace,
                                s,
                                target,
                                l.length - 1,
                                unknown,
                                initial)

    (succ match {
      case Nil() => false
      case Cons(x, xs) if (!currentTrace.contains(x)) =>
        if (addStateToTrace(currentTrace, s, x) &&
            noTarget(currentTrace, target, x) &&
            simpleAppend(currentTrace, x)) {

          kReachabilityCheck(currentTrace :+ x,
                             s,
                             target,
                             l.length - 1,
                             initial) match {
            case Trace(t) => true
            case Unknown =>
              if (x == l.head) {
                completeTrace(l, s, initial, target, currentTrace :+ x) &&
                false
              } else
                completeTraceExploreSucc(l,
                                         s,
                                         xs,
                                         target,
                                         true,
                                         initial,
                                         currentTrace)
            case Unreachable =>
              if (x == l.head) {
                completeTrace(l, s, initial, target, currentTrace :+ x) &&
                false
              } else
                completeTraceExploreSucc(
                  l,
                  s,
                  xs,
                  target,
                  unknown,
                  initial,
                  currentTrace) //exploreSuccessors(xs, currentTrace, s, target, k, unknown, initial)
          }
        } else false

      case Cons(x, xs) => //exploreSuccessors(xs, currentTrace, s, target, k, unknown, initial)
        if (x == l.head)
          false
        else {
          completeTraceExploreSucc(l,
                                   s,
                                   xs,
                                   target,
                                   unknown,
                                   initial,
                                   currentTrace)
        }
    }) && (res match {
      case Trace(_) => true
      case _ => false
    })
  }.holds

  def completeTraceInit(l: List[State],
                        s: System,
                        initial: State,
                        target: State): Boolean = {
    require(
      isTrace(s, l) &&
        !l.isEmpty &&
        l.last == target &&
        l.head == initial
    )
    val res =
      kReachabilityCheck(List(initial),
                         s,
                         target,
                         simpleTrace(s, l).length - 1,
                         initial)

    completeTrace(simpleTrace(s, l), s, initial, target, List(initial)) &&
    (res match {
      case Trace(t) => true
      case _ => false
    })

  }.holds

  def statesToString(l: List[State]): String = {
    decreases(l)
    l match {
      case Nil() => ""
      case Cons(x, xs) => x.toString + "\n" + statesToString(xs)
    }
  }

  //create equivalent cycle free trace for given trace
  def simpleTrace(s: System, l: List[State]): List[State] = {
    require(isTrace(s, l))
    decreases((l.length, BigInt(0)))
    l match {
      case Nil() => l
      case Cons(x, xs) =>
        if (!xs.contains(x)) {
          simpleNoAdd(s, xs, x) && simplePrepend(x, simpleTrace(s, xs))
          Cons(x, simpleTrace(s, xs))
        } else {
          removeCycleLast(s, xs, x)
          simpleTrace(s, Cons(x, removeCycle(s, xs, x)))
        }
    }
  } ensuring (res =>
                simple(res) && (l.isEmpty || (!res.isEmpty && res.head == l.head &&
                  isTrace(s, res) && !res.isEmpty && res.last == l.last)))

  def removeCycle(s: System,
                  l: List[State],
                  duplicateState: State): List[State] = {
    require(isTrace(s, l) && l.contains(duplicateState))
    decreases(l)
    l match {
      case Cons(x, xs) =>
        if (x == duplicateState)
          xs
        else {
          removeCycle(s, xs, duplicateState)
        }
    }
  } ensuring (res =>
                res.length < l.length &&
                isTrace(s, res) && (res.isEmpty || s.transitions.contains(
                  (duplicateState, res.head))))

  def simplePrepend[X](x: X, l: List[X]): Boolean = {
    require(simple(l) && !l.contains(x))
    simple(Cons(x, l))
  }.holds

  def simpleNoAdd(s: System, l: List[State], st: State): Boolean = {
    require(isTrace(s, l) && !l.contains(st))
    decreases((l.length, BigInt(1)))
    val sim = simpleTrace(s, l)

    check(l match {
      case Nil() => true
      case Cons(x, xs) =>
        if (!xs.contains(x)) {
          simpleNoAdd(s, xs, st)
        } else {
          removeCycleNoAdd(s, xs, x, st) && simpleNoAdd(
            s,
            Cons(x, removeCycle(s, xs, x)),
            st)
        }
    })

    !sim.contains(st)
  }.holds

  // @induct
  def removeCycleNoAdd(s: System,
                       l: List[State],
                       duplicateState: State,
                       st: State): Boolean = {
    require(isTrace(s, l) && l.contains(duplicateState) && !l.contains(st))
    decreases(l)

    val rc = removeCycle(s, l, duplicateState)

    check(l.isEmpty || l.head == duplicateState || removeCycleNoAdd(s, l.tail, duplicateState, st))

    !rc.contains(st)
  }.holds

  // @induct
  def removeCycleLast(s: System,
                      l: List[State],
                      duplicateState: State): Boolean = {
    require(isTrace(s, l) && l.contains(duplicateState))
    decreases(l)

    check(l.isEmpty || l.head == duplicateState || removeCycleLast(s, l.tail, duplicateState))

    l.last == (Cons(duplicateState, removeCycle(s, l, duplicateState))).last
  }.holds

  def simpleAppend[X](@induct t: List[X], x: X): Boolean = {
    require(simple(t) && !t.contains(x))

    check(t.isEmpty || simpleAppend(t.tail, x))

    simple(t :+ x)
  }.holds
}
