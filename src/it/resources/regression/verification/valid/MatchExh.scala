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

}
