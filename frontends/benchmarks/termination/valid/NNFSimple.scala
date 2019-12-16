/* Copyright 2009-2019 EPFL, Lausanne */

import stainless.lang._
import stainless.annotation._

object NNFSimple {

  sealed abstract class Formula
  case class And(lhs: Formula, rhs: Formula) extends Formula
  case class Or(lhs: Formula, rhs: Formula) extends Formula
  case class Implies(lhs: Formula, rhs: Formula) extends Formula
  case class Not(f: Formula) extends Formula
  case class Literal(id: BigInt) extends Formula

  def simplify(f: Formula): Formula = (f match {
    case And(lhs, rhs) => And(simplify(lhs), simplify(rhs))
    case Or(lhs, rhs) => Or(simplify(lhs), simplify(rhs))
    case Implies(lhs, rhs) => Or(Not(simplify(lhs)), simplify(rhs))
    case Not(f) => Not(simplify(f))
    case Literal(_) => f
  }) ensuring(isSimplified(_))

  def isSimplified(f: Formula): Boolean = f match {
    case And(lhs, rhs) => isSimplified(lhs) && isSimplified(rhs)
    case Or(lhs, rhs) => isSimplified(lhs) && isSimplified(rhs)
    case Implies(_,_) => false
    case Not(f) => isSimplified(f)
    case Literal(_) => true
  }

  import stainless.math.max

  // def measure(f: Formula): BigInt = f match {
  //   case Or(lhs, rhs) =>
  //     size(f) + max(size(lhs), size(rhs))
  //   case Implies(lhs, rhs) =>
  //     size(f) + size(Or(Not(lhs), rhs))
  //   case _ => 0
  // }

  // def orImpliesMeasure: BigInt = measure(Or(Implies(Literal(0), Literal(0)), Literal(0)))

  // def size(f: Formula): BigInt = {
  //   decreases(f)
  //   f match {
  //     case And(lhs, rhs) => 1 + size(lhs) + size(rhs)
  //     case Or(lhs, rhs) => 1 + size(lhs) + size(rhs)
  //     case Implies(lhs, rhs) => 1 + size(lhs) + size(rhs)
  //     case Not(f) => 1 + size(f)
  //     case Literal(b) => stainless.math.abs(b)
  //   }
  // } ensuring { _ >= 0 }

  @extern
  def b: Boolean = true

  def simpleNNF(formula: Formula): Formula = {
    // decreases(measure(formula))
    formula match {
      // case Or(lhs, rhs) => Or(if (b) simpleNNF(lhs) else simpleNNF(rhs), simpleNNF(rhs))
      case Or(lhs, rhs) => Or(simpleNNF(lhs), simpleNNF(rhs))
      case Implies(lhs, rhs) => simpleNNF(Or(Not(lhs), rhs))
      case _ => formula
    }
  }

  def isNNF(f: Formula): Boolean = f match {
    case And(lhs, rhs) => isNNF(lhs) && isNNF(rhs)
    case Or(lhs, rhs) => isNNF(lhs) && isNNF(rhs)
    case Implies(lhs, rhs) => false
    case Not(Literal(_)) => true
    case Not(_) => false
    case Literal(_) => true
  }

  def evalLit(id : BigInt) : Boolean = (id == 42) // could be any function

  def eval(f: Formula) : Boolean = f match {
    case And(lhs, rhs) => eval(lhs) && eval(rhs)
    case Or(lhs, rhs) => eval(lhs) || eval(rhs)
    case Implies(lhs, rhs) => !eval(lhs) || eval(rhs)
    case Not(f) => !eval(f)
    case Literal(id) => evalLit(id)
  }

  @induct
  def simplifySemantics(f: Formula) : Boolean = {
    eval(f) == eval(simplify(f))
  }.holds

  // Note that matching is exhaustive due to precondition.
  def vars(f: Formula): Set[BigInt] = {
    require(isNNF(f))
    f match {
      case And(lhs, rhs) => vars(lhs) ++ vars(rhs)
      case Or(lhs, rhs) => vars(lhs) ++ vars(rhs)
      case Not(Literal(i)) => Set[BigInt](i)
      case Literal(i) => Set[BigInt](i)
    }
  }

  @induct
  def simplifyIsStable(f: Formula) : Boolean = {
    require(isSimplified(f))
    simplify(f) == f
  }.holds
}
