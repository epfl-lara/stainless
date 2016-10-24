/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._
import leon.collection._
import leon.annotation._

object TraceInductTacticTest {
  
  def contains(l: List[BigInt], set: Set[BigInt]): Boolean = {
    l match {
      case Cons(x, xs) => set.contains(x) && contains(xs, set)
      case Nil() => true
    }    
  }
  
  @traceInduct
  def monotonicity(l: List[BigInt], set1: Set[BigInt], set2: Set[BigInt]): Boolean = {
    (contains(l, set1) && set1.subsetOf(set2)) ==> contains(l, set2)
  } holds   
}
