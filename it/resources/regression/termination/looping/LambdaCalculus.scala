/* Copyright 2009-2016 EPFL, Lausanne */

import stainless.lang._
import stainless.collection._
import stainless._

object LambdaCalculus {
  abstract class Term
  case class Var(x: BigInt) extends Term
  case class Abs(x: BigInt, body: Term) extends Term
  case class App(func: Term, arg: Term) extends Term
  
  def fv(t: Term): Set[BigInt] = t match {
    case Var(x) => Set(x)
    case Abs(x, body) => fv(body) ++ Set(x)
    case App(func, arg) => fv(func) ++ fv(arg)
  }
  
  // [x->u]t
  def subst(x: BigInt, u: Term, t: Term): Term = t match {
    case Var(y) => if (x == y) u else t
    case Abs(y, body) => if (x == y) t else Abs(y, subst(x, u, body))
    case App(f, a) => App(subst(x, u, f), subst(x, u, a))
  }
  
  /* Termination checker (LoopProcessor) says:
  ✗ Non-terminating for call: looping_eval(App(Abs(0, App(Var(0), Var(0))), Abs(0, App(Var(0), Var(0)))))
  i.e.
  (λx. x x)(λx. x x)
  This is the well-known "omega".
  */
  // big step call-by-value looping_evaluation
  def looping_eval(t: Term): Option[Term] = (t match {
    case App(t1, t2) => looping_eval(t1) match {
      case Some(Abs(x, body)) => looping_eval(t2) match {
        case Some(v2) => looping_eval(subst(x, v2, body))
        case None() => None[Term]()
      }
      case _ => None[Term]() // stuck
    }
    case _ => Some(t) // Abs or Var, already a value
  }) ensuring { res => res match {
    case Some(t) => isValue(t)
    case None() => true
  }}

  def isValue(t: Term): Boolean = t match {
    case Var(x) => true
    case Abs(x, body) => true
    case App(f, a) => false
  }

}
