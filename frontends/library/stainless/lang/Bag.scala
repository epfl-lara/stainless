/* Copyright 2009-2021 EPFL, Lausanne */

package stainless.lang

import stainless.annotation._

object Bag {
  @library @inline
  def empty[T] (using CanEqual[T, T])= Bag[T]()

  @ignore
  def apply[T](elems: (T, BigInt)*)(using CanEqual[T, T]) = {
    new Bag[T](scala.collection.immutable.Map[T, BigInt](elems*))
  }
}

@ignore
case class Bag[T](theBag: scala.collection.immutable.Map[T, BigInt]) derives CanEqual {
  def +(a: T)(using CanEqual[T, T]): Bag[T] = new Bag(theBag + (a -> (theBag.getOrElse(a, BigInt(0)) + 1)))
  def ++(that: Bag[T])(using CanEqual[T, T]): Bag[T] = new Bag[T]((theBag.keys ++ that.theBag.keys).toSet.map { (k: T) =>
    k -> (theBag.getOrElse(k, BigInt(0)) + that.theBag.getOrElse(k, BigInt(0)))
  }.toMap)

  def --(that: Bag[T])(using CanEqual[T, T]): Bag[T] = new Bag[T](theBag.flatMap { case (k,v) =>
    val res = v - that.get(k)
    if (res <= 0) Nil else List(k -> res)
  })

  def &(that: Bag[T])(using CanEqual[T, T]): Bag[T] = new Bag[T](theBag.flatMap { case (k,v) =>
    val res = v min that.get(k)
    if (res <= 0) Nil else List(k -> res)
  })

  def get(a: T)(using CanEqual[T, T]): BigInt = theBag.getOrElse(a, BigInt(0))
  def apply(a: T)(using CanEqual[T, T]): BigInt = get(a)
  def isEmpty: Boolean = theBag.isEmpty
}

