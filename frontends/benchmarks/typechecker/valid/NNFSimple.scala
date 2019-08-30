/* Copyright 2009-2018 EPFL, Lausanne */

import stainless.lang._
import stainless.annotation._

object NNFSimple {

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
  def simpleNNFMeasure(formula: Formula): BigInt = {
    decreases(formula)
    formula match {
      case And(lhs, rhs) => simpleNNFMeasure(lhs) + simpleNNFMeasure(rhs) + 1
      case Or(lhs, rhs) => simpleNNFMeasure(lhs) + simpleNNFMeasure(rhs) + 1
      case Implies(lhs, rhs) => simpleNNFMeasure(lhs) + simpleNNFMeasure(rhs) + 3
      case Not(f) => simpleNNFMeasure(f) + 1
      case Literal(_) => BigInt(0)
    }
  } ensuring((res: BigInt) => res >= 0)

  def simpleNNF(formula: Formula): Formula = {
    decreases(simpleNNFMeasure(formula))
    formula match {
      case Or(lhs, rhs) => Or(simpleNNF(lhs), simpleNNF(rhs))
      case Implies(lhs, rhs) => simpleNNF(Or(Not(lhs), rhs))
      case _ => formula
    }
  }

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
  }.holds

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

  @induct
  def simplifyIsStable(f: Formula) : Boolean = {
    require(isSimplified(f))
    simplify(f) == f
  }.holds
}
