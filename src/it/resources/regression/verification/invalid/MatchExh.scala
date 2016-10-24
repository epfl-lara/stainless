/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._
import leon.collection._

object MatchExh {
  
  def exh1(i: Int) = i match {
    case 1 => 2
    case 0 => 2
    case _ => 2
  }

  def exh2[A](l: List[A]) = l match {
    case Nil() => 0
    case Cons(a, Nil()) => 1
    case Cons(a, _) => 2
  }

  def err1(i: Int) = i match {
    case 1 => 2
    case 0 => 42
  }

  def err2[A](l: List[A]) = l match {
    case Nil() => 0
    case Cons(a, Nil()) => 1
    case Cons(a, Cons(b, _)) if a == b => 2
  }

  def err3(l: List[BigInt]) = l match {
    case Nil() => 0
    case Cons(BigInt(0), Nil()) => 0
    case Cons(_, Cons(_, _)) => 1
  }

}
