/* Copyright 2009-2015 EPFL, Lausanne */

import leon.lang._
import leon.annotation._

object PropositionalLogic { 

  sealed abstract class Formula
  case class And(lhs: Formula, rhs: Formula) extends Formula
  case class Or(lhs: Formula, rhs: Formula) extends Formula
  case class Implies(lhs: Formula, rhs: Formula) extends Formula
  case class Not(f: Formula) extends Formula
  case class Literal(id: BigInt) extends Formula

  def simplify(f: Formula): Formula = (f match {
    case Implies(lhs, rhs) => Or(Not(simplify(lhs)), simplify(rhs))
    case _ => f
  }) ensuring(isSimplified(_))

  def isSimplified(f: Formula): Boolean = f match {
    case And(lhs, rhs) => isSimplified(lhs) && isSimplified(rhs)
    case Or(lhs, rhs) => isSimplified(lhs) && isSimplified(rhs)
    case Implies(_,_) => false
    case Not(f) => isSimplified(f)
    case Literal(_) => true
  }

  def isNNF(f: Formula): Boolean = f match {
    case And(lhs, rhs) => isNNF(lhs) && isNNF(rhs)
    case Or(lhs, rhs) => isNNF(lhs) && isNNF(rhs)
    case Implies(lhs, rhs) => isNNF(lhs) && isNNF(rhs)
    case Not(Literal(_)) => true
    case Not(_) => false
    case Literal(_) => true
  }


  // @induct
  // def wrongCommutative(f: Formula) : Boolean = {
  //   nnf(simplify(f)) == simplify(nnf(f))
  // }.holds

 def simplifyBreaksNNF(f: Formula) : Boolean = {
    require(isNNF(f))
    isNNF(simplify(f))
  }.holds
}
