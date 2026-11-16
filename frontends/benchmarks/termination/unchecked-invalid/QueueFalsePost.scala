/* Copyright 2009-2026 EPFL, Lausanne */

import stainless._
import stainless.lang._
import stainless.collection._

// Queue.scala, where looping_3 has a false postcondition. The termination proof of the cycle must not
// assume it, as looping_3 never returns on the calls that the cycle makes.
sealed abstract class FQueue[T] {

   def looping_1: BigInt = {
      this match {
         case FQEmpty() => BigInt(0)
         case FQCons(f, r) => f.size + r.size
      }
  }.ensuring(res => res == this.looping_2.size && res >= 0)

   def looping_2: List[T] = (this match {
      case FQEmpty() => Nil[T]()
      case FQCons(f, r) => f ++ r.reverse
   }).ensuring (resOne => this.looping_3 == resOne.content && resOne.size == this.looping_1 && resOne.size >= 0)

   def looping_3: Set[T] = (this match {
      case FQEmpty() => Set[T]()
      case FQCons(f, r) => f.content ++ r.content
   }).ensuring (res => res == this.looping_2.content && false)
}

case class FQCons[T](f : List[T], r: List[T]) extends FQueue[T]
case class FQEmpty[T]() extends FQueue[T]
