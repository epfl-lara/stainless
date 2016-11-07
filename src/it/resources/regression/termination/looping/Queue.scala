/* Copyright 2009-2016 EPFL, Lausanne */

import stainless._
import stainless.lang._
import stainless.collection._

sealed abstract class Queue[T] {

   def looping_1: BigInt = {
      this match {
         case QEmpty() => BigInt(0)
         case QCons(f, r) => f.size + r.size
      }
   } ensuring (res => res == this.looping_2.size && res >= 0)

   def looping_2: List[T] = (this match {
      case QEmpty() => Nil[T]()
      case QCons(f, r) => f ++ r.reverse
   }) ensuring (resOne => this.looping_3 == resOne.content && resOne.size == this.looping_1 && resOne.size >= 0)

   def looping_3: Set[T] = (this match {
      case QEmpty() => Set[T]()
      case QCons(f, r) => f.content ++ r.content
   }) ensuring (res => res == this.looping_2.content)
}

case class QCons[T](f : List[T], r: List[T]) extends Queue[T]
case class QEmpty[T]() extends Queue[T]
