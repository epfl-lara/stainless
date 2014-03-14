/* Copyright 2009-2014 EPFL, Lausanne */

import leon.lang._

/** This benchmarks tests some potential issues with the legacy "bestRealType" function, which was original introduced to work around
 * Scala's well-too-precise-for-Leon type inference. */
object BestRealTypes {
  sealed abstract class Num
  case class Zero() extends Num
  case class Succ(pred : Num) extends Num

  case class Wrapper(num : Num)

  def boolToNum(b : Boolean) : Num = if(b) {
    Zero()
  } else {
    Succ(Zero())
  }

  // This requires computing the "bestRealTypes" of w1 and w2.
  def zipWrap(w1 : Wrapper, w2 : Wrapper) : (Wrapper,Wrapper) = (w1, w2)

  def somethingToProve(b : Boolean) : Boolean = {
    val (z1,z2) = zipWrap(Wrapper(boolToNum(b)), Wrapper(boolToNum(!b)))
    z1.num == Zero() || z2.num == Zero() 
  }.holds
}
