/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._ 
object Unap {
  def unapply[A, B](i: (Int, B, A)): Option[(A, B)] = 
    if (i._1 == 0) None() else Some((i._3, i._2))
}

object Unapply {

  sealed abstract class Bool
  case class True() extends Bool
  case class False() extends Bool
  
  def not(b: Bool): Bool = b match {
    case True() => False()
    case False() => True()
  }

  def bar: Bool = { (42, True().asInstanceOf[Bool], ()) match {
    case Unap(_, b) if b == True() => b
    case Unap((), b) => not(b)
  }} ensuring { res => res == True() }
}
