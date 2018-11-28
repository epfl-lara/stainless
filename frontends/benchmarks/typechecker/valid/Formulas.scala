/* Copyright 2009-2018 EPFL, Lausanne */

import stainless.lang._
import stainless._

object Formulas {
  sealed abstract class Expr
  case class And(lhs: Expr, rhs: Expr) extends Expr
  case class Or(lhs: Expr, rhs: Expr) extends Expr
  case class Implies(lhs: Expr, rhs: Expr) extends Expr
  case class Not(e : Expr) extends Expr
  case class BoolLiteral(i: BigInt) extends Expr

  def exists(e: Expr, f: Expr => Boolean): Boolean = {
    decreases(e)
    f(e) || (e match {
      case And(lhs, rhs) => exists(lhs, f) || exists(rhs, f)
      case Or(lhs, rhs) => exists(lhs, f) || exists(rhs, f)
      case Implies(lhs, rhs) => exists(lhs, f) || exists(rhs, f)
      case Not(e) => exists(e, f)
      case _ => false
    })
  }

  def existsImplies(e: Expr): Boolean = {
    decreases(e)
    e.isInstanceOf[Implies] || (e match {
      case And(lhs, rhs) => existsImplies(lhs) || existsImplies(rhs)
      case Or(lhs, rhs) => existsImplies(lhs) || existsImplies(rhs)
      case Implies(lhs, rhs) => existsImplies(lhs) || existsImplies(rhs)
      case Not(e) => existsImplies(e)
      case _ => false
    })
  }

  sealed abstract class Value
  case class BoolValue(b: Boolean) extends Value
  case class IntValue(i: BigInt) extends Value
  case object Error extends Value

  def desugar(e: Expr): Expr = {
    decreases(e)
    e match {
      case And(lhs, rhs) => And(desugar(lhs), desugar(rhs))
      case Or(lhs, rhs) => Or(desugar(lhs), desugar(rhs))
      case Implies(lhs, rhs) =>
        Or(Not(desugar(lhs)), desugar(rhs))
      case Not(e) => Not(desugar(e))
      case e => e
    }
  } ensuring { out =>
    !existsImplies(out) &&
    !exists(out, f => f.isInstanceOf[Implies])
  }
}
