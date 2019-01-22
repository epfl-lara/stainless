/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.lang
import stainless.annotation._

import scala.language.implicitConversions

object Set {
  @library @inline
  def empty[T] = Set[T]()

  @ignore
  def apply[T](elems: T*) = {
    new Set[T](scala.collection.immutable.Set[T](elems : _*))
  }
  
  @extern @library
  def mkString[A](map: Set[A], infix: String, fA : A => String) = {
    map.theSet.map(fA).toList.sorted.mkString(infix)
  }
}

@ignore
case class Set[T](val theSet: scala.collection.immutable.Set[T]) {
  def +(a: T): Set[T] = new Set[T](theSet + a)
  def ++(a: Set[T]): Set[T] = new Set[T](theSet ++ a.theSet)
  def -(a: T): Set[T] = new Set[T](theSet - a)
  def --(a: Set[T]): Set[T] = new Set[T](theSet -- a.theSet)
  def size: BigInt = theSet.size
  def contains(a: T): Boolean = theSet.contains(a)
  def isEmpty: Boolean = theSet.isEmpty
  def subsetOf(b: Set[T]): Boolean = theSet.subsetOf(b.theSet)
  def &(a: Set[T]): Set[T] = new Set[T](theSet & a.theSet)
}

