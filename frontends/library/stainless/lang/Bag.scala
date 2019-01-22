/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.lang

import scala.language.implicitConversions

import stainless.annotation._

object Bag {
  @library @inline
  def empty[T] = Bag[T]()

  @ignore
  def apply[T](elems: (T, BigInt)*) = {
    new Bag[T](scala.collection.immutable.Map[T, BigInt](elems : _*))
  }
}

@ignore
case class Bag[T](theBag: scala.collection.immutable.Map[T, BigInt]) {
  def +(a: T): Bag[T] = new Bag(theBag + (a -> (theBag.getOrElse(a, BigInt(0)) + 1)))
  def ++(that: Bag[T]): Bag[T] = new Bag[T]((theBag.keys ++ that.theBag.keys).toSet.map { (k: T) =>
    k -> (theBag.getOrElse(k, BigInt(0)) + that.theBag.getOrElse(k, BigInt(0)))
  }.toMap)

  def --(that: Bag[T]): Bag[T] = new Bag[T](theBag.flatMap { case (k,v) =>
    val res = v - that.get(k)
    if (res <= 0) Nil else List(k -> res)
  })

  def &(that: Bag[T]): Bag[T] = new Bag[T](theBag.flatMap { case (k,v) =>
    val res = v min that.get(k)
    if (res <= 0) Nil else List(k -> res)
  })

  def get(a: T): BigInt = theBag.getOrElse(a, BigInt(0))
  def apply(a: T): BigInt = get(a)
  def isEmpty: Boolean = theBag.isEmpty
}

