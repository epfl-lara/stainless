/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._

object Unap1 {
  def unapply[A, B](i: (Int, B, A)): Option[(A, B)] = 
    if (i._1 == 0) None() else Some((i._3, i._2))
}
  
object Unapply1 {

  sealed abstract class Bool
  case class True() extends Bool
  case class False() extends Bool
  
  def bar: Bool = { (42, False().asInstanceOf[Bool], ()) match {
    case Unap1(_, b) if b == True() => b
    case Unap1((), b) => b
  }} ensuring { res => res == True() }
  
}
