/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._ 
object Unap2 {
  def unapply[A, B](i: (Int, B, A)): Option[(A, B)] = 
    if (i._1 == 0) None() else Some((i._3, i._2))
}
 
object Unapply {

  sealed abstract class Bool
  case class True() extends Bool
  case class False() extends Bool

  def bar: Bool = { (42, False().asInstanceOf[Bool], ()) match {
    case Unap2(_, b) if b == True() => b
  }} ensuring { res => res == True() }
}
