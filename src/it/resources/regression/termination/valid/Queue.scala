/* Copyright 2009-2016 EPFL, Lausanne */

import stainless._
import stainless.lang._
import stainless.collection._

sealed abstract class Queue[T] {

   def size: BigInt = {
      this match {
         case QEmpty() => BigInt(0)
         case QCons(f, r) => f.size + r.size
      }
   } ensuring (res => res == this.toList.size && res >= 0)

   def toList: List[T] = (this match {
      case QEmpty() => Nil[T]()
      case QCons(f, r) => f ++ r.reverse
   }) ensuring (resOne => this.content == resOne.content && resOne.size >= 0)

   def content: Set[T] = this match {
      case QEmpty() => Set()
      case QCons(f, r) => f.content ++ r.content
   }
}

case class QCons[T](f : List[T], r: List[T]) extends Queue[T]
case class QEmpty[T]() extends Queue[T]
