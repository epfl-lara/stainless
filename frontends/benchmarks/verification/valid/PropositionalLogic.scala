/* Copyright 2009-2024 EPFL, Lausanne */

import stainless.lang.*
import stainless.annotation.*

object PropositionalLogic:

  sealed abstract class Formula:
    def size: BigInt = { // just to be clear what measure we are using
      this match
        case And(l, r)  => l.size + r.size + 1
        case Or(l, r)   => l.size + r.size + 1
        case Not(f)     => f.size + 1
        case Implies(l, r) => l.size + r.size + 1
        case Literal(_) => BigInt(1)
    }.ensuring(res => res >= 1)

  case class And(lhs: Formula, rhs: Formula) extends Formula
  case class Or(lhs: Formula, rhs: Formula) extends Formula
  case class Implies(lhs: Formula, rhs: Formula) extends Formula
  case class Not(f: Formula) extends Formula
  case class Literal(id: Int) extends Formula

  def simplify(f: Formula): Formula = {
    decreases(f.size)
    f match 
      case And(lhs, rhs) => And(simplify(lhs), simplify(rhs))
      case Or(lhs, rhs) => Or(simplify(lhs), simplify(rhs))
      case Implies(lhs, rhs) => Or(Not(simplify(lhs)), simplify(rhs))
      case Not(f) => Not(simplify(f))
      case Literal(_) => f
  }.ensuring(isSimplified(_))

  def isSimplified(f: Formula): Boolean = {
    decreases(f.size)
    f match 
      case And(lhs, rhs) => isSimplified(lhs) && isSimplified(rhs)
      case Or(lhs, rhs) => isSimplified(lhs) && isSimplified(rhs)
      case Implies(_,_) => false
      case Not(f) => isSimplified(f)
      case Literal(_) => true
  }

  def nnf(formula: Formula): Formula = {
    require(isSimplified(formula))
    decreases(formula.size)
    formula match 
      case And(lhs, rhs) => And(nnf(lhs), nnf(rhs))
      case Or(lhs, rhs) => Or(nnf(lhs), nnf(rhs))
      case Not(And(lhs, rhs)) => Or(nnf(Not(lhs)), nnf(Not(rhs)))
      case Not(Or(lhs, rhs)) => And(nnf(Not(lhs)), nnf(Not(rhs)))
      case Not(Implies(lhs, rhs)) => And(nnf(lhs), nnf(Not(rhs)))
      case Not(Not(f)) => nnf(f)
      case Not(Literal(_)) => formula
      case Literal(_) => formula
  }.ensuring(isNNF(_))

  def isNNF(f: Formula): Boolean = {
    decreases(f.size)
    f match 
      case And(lhs, rhs) => isNNF(lhs) && isNNF(rhs)
      case Or(lhs, rhs) => isNNF(lhs) && isNNF(rhs)
      case Implies(lhs, rhs) => false
      case Not(Literal(_)) => true
      case Not(_) => false
      case Literal(_) => true
  }.ensuring(res => !res || isSimplified(f))

  def vars(f: Formula): Set[Int] = {
    require(isNNF(f))
    decreases(f.size)
    f match {
      case And(lhs, rhs) => vars(lhs) ++ vars(rhs)
      case Or(lhs, rhs) => vars(lhs) ++ vars(rhs)
      case Not(Literal(i)) => Set[Int](i)
      case Literal(i) => Set[Int](i)
    }
  }

  def fv(f : Formula) = { vars(nnf(simplify(f))) }

  @induct
  def nnfIsStable(f: Formula) : Boolean = {
    require(isNNF(f))
    nnf(f) == f
  }.holds
  
  @induct
  def simplifyIsStable(f: Formula) : Boolean = {
    require(isSimplified(f))
    simplify(f) == f
  }.holds


end PropositionalLogic 
