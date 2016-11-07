/* Copyright 2009-2016 EPFL, Lausanne */

import stainless.annotation._
import stainless.lang._

object Interpret {
  abstract class BoolTree
  case class Eq(t1 : IntTree, t2 : IntTree) extends BoolTree
  case class And(t1 : BoolTree, t2 : BoolTree) extends BoolTree
  case class Not(t : BoolTree) extends BoolTree

  abstract class IntTree
  case class Const(c:Int) extends IntTree
  case class Var() extends IntTree
  case class Plus(t1 : IntTree, t2 : IntTree) extends IntTree
  case class Minus(t1 : IntTree, t2 : IntTree) extends IntTree
  case class Less(t1 : IntTree, t2 : IntTree) extends BoolTree
  case class If(cond : BoolTree, t : IntTree, e : IntTree) extends IntTree

  def repOk(t : IntTree) : Boolean = {
    true
  }

  def beval(t:BoolTree, x0 : Int) : Boolean = {
    t match {
      case Less(t1, t2) => ieval(t1,x0) < ieval(t2,x0)
      case Eq(t1, t2) => ieval(t1,x0) == ieval(t2,x0)
      case And(t1, t2) => beval(t1,x0) && beval(t2,x0)
      case Not(t1) => !beval(t1,x0)
    }
  }

  def ieval(t:IntTree, x0 : Int) : Int = {
    t match {
      case Const(c) => c
      case Var() => x0
      case Plus(t1,t2) => ieval(t1,x0) + ieval(t2,x0)
      case Minus(t1, t2) => ieval(t1,x0) - ieval(t2,x0)
      case If(c,t1,t2) => if (beval(c,x0)) ieval(t1,x0) else ieval(t2,x0)
    }
  }
  def computesPositive(t : IntTree) : Boolean = {
    ieval(t,0) >= 0 &&
    ieval(t,1) >= 0 &&
    ieval(t,-1) >= 0 &&
    ieval(t,-2) >= 0 &&
    ieval(t,2) >= 0
  }
  def identityForPositive(t : IntTree) : Boolean = {
    ieval(t, 5) == 5 &&
    ieval(t, 33) == 33 &&
    ieval(t, 0) == 0 &&
    ieval(t, -1) == 1 &&
    ieval(t, -2) == 2
  }

  def treeBad(t : IntTree) : Boolean = {
    !(repOk(t) && computesPositive(t) && identityForPositive(t))
  }.holds

  def thereIsGoodTree() : Boolean = {
    !treeBad(If(Less(Const(0),Var()), Var(), Minus(Const(0),Var())))
  }.holds

  @ignore
  def main(args : Array[String]) {
    thereIsGoodTree()
  }
}
