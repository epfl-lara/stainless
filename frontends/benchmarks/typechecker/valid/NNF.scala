/* Copyright 2009-2018 EPFL, Lausanne */

import stainless.lang._
import stainless.annotation._

object NNF {

  sealed abstract class Formula
  case class And(lhs: Formula, rhs: Formula) extends Formula
  case class Or(lhs: Formula, rhs: Formula) extends Formula
  case class Implies(lhs: Formula, rhs: Formula) extends Formula
  case class Not(f: Formula) extends Formula
  case class Literal(id: BigInt) extends Formula

  def simplify(f: Formula): Formula = {
    decreases(f)
    f match {
      case And(lhs, rhs) => And(simplify(lhs), simplify(rhs))
      case Or(lhs, rhs) => Or(simplify(lhs), simplify(rhs))
      case Implies(lhs, rhs) => Or(Not(simplify(lhs)), simplify(rhs))
      case Not(f) => Not(simplify(f))
      case Literal(_) => f
    }
  } ensuring(isSimplified(_))

  def isSimplified(f: Formula): Boolean = {
    decreases(f)
    f match {
      case And(lhs, rhs) => isSimplified(lhs) && isSimplified(rhs)
      case Or(lhs, rhs) => isSimplified(lhs) && isSimplified(rhs)
      case Implies(_,_) => false
      case Not(f) => isSimplified(f)
      case Literal(_) => true
    }
  }

  // Measure used to prove termination of `nnf`
  // Implies is given more weight than other nodes
  def nnfMeasure(formula: Formula): BigInt = {
    decreases(formula)
    formula match {
      case And(lhs, rhs) => nnfMeasure(lhs) + nnfMeasure(rhs) + 1
      case Or(lhs, rhs) => nnfMeasure(lhs) + nnfMeasure(rhs) + 1
      case Implies(lhs, rhs) => nnfMeasure(lhs) + nnfMeasure(rhs) + 3
      case Not(f) => nnfMeasure(f) + 1
      case Literal(_) => BigInt(0)
    }
  } ensuring((res: BigInt) => res >= 0)

  def nnf(formula: Formula): Formula = {
    decreases(nnfMeasure(formula))
    formula match {
      case And(lhs, rhs) => And(nnf(lhs), nnf(rhs))
      case Or(lhs, rhs) => Or(nnf(lhs), nnf(rhs))
      case Implies(lhs, rhs) => nnf(Or(Not(lhs), rhs))
      case Not(And(lhs, rhs)) => Or(nnf(Not(lhs)), nnf(Not(rhs)))
      case Not(Or(lhs, rhs)) => And(nnf(Not(lhs)), nnf(Not(rhs)))
      case Not(Implies(lhs, rhs)) => And(nnf(lhs), nnf(Not(rhs)))
      case Not(Not(f)) => nnf(f)
      case Not(Literal(_)) => formula
      case Literal(_) => formula
    }
  } ensuring(isNNF(_))

  def isNNF(f: Formula): Boolean = {
    decreases(f)
    f match {
      case And(lhs, rhs) => isNNF(lhs) && isNNF(rhs)
      case Or(lhs, rhs) => isNNF(lhs) && isNNF(rhs)
      case Implies(lhs, rhs) => false
      case Not(Literal(_)) => true
      case Not(_) => false
      case Literal(_) => true
    }
  }

  def evalLit(id : BigInt) : Boolean = (id == 42) // could be any function
  def eval(f: Formula) : Boolean = {
    decreases(f)
    f match {
      case And(lhs, rhs) => eval(lhs) && eval(rhs)
      case Or(lhs, rhs) => eval(lhs) || eval(rhs)
      case Implies(lhs, rhs) => !eval(lhs) || eval(rhs)
      case Not(f) => !eval(f)
      case Literal(id) => evalLit(id)
    }
  }

  @induct
  def simplifySemantics(f: Formula) : Boolean = {
    eval(f) == eval(simplify(f))
  } holds

  // Note that matching is exhaustive due to precondition.
  def vars(f: Formula): Set[BigInt] = {
    require(isNNF(f))
    decreases(f)
    f match {
      case And(lhs, rhs) => vars(lhs) ++ vars(rhs)
      case Or(lhs, rhs) => vars(lhs) ++ vars(rhs)
      case Not(Literal(i)) => Set[BigInt](i)
      case Literal(i) => Set[BigInt](i)
    }
  }

  def fv(f : Formula) = { vars(nnf(f)) }

  @induct
  def wrongCommutative(f: Formula) : Boolean = {
    nnf(simplify(f)) == simplify(nnf(f))
  } // holds

  @induct
  def simplifyPreservesNNF(f: Formula) : Boolean = {
    require(isNNF(f))
    isNNF(simplify(f))
  } holds

  @induct
  def nnfIsStable(f: Formula) : Boolean = {
    require(isNNF(f))
    nnf(f) == f
  } holds

  @induct
  def simplifyIsStable(f: Formula) : Boolean = {
    require(isSimplified(f))
    simplify(f) == f
  } holds
}
