/* Copyright 2009-2022 EPFL, Lausanne */

package stainless
package collection

import stainless.annotation._
import stainless.lang._
import StaticChecks._

/** List-backed Map implementation */

@library
case class ListMap[A, B](toList: List[(A, B)]) {
  require(ListOps.noDuplicate(toList.map(_._1)))

  def isEmpty: Boolean = toList.isEmpty

  def nonEmpty: Boolean = !isEmpty

  def head: (A, B) = {
    require(!isEmpty)
    toList.head
  }

  def tail: ListMap[A, B] = {
    require(!isEmpty)
    ListMap(toList.tail)
  }

  def contains(key: A): Boolean = {
    get(key).isDefined
  }

  def get(key: A): Option[B] = {
    toList.find(_._1 == key).map(_._2)
  }

  def keysOf(value: B): List[A] = {
    toList.filter(_._2 == value).map(_._1)
  }

  def apply(key: A): B = {
    require(contains(key))
    get(key).get
  }

  def +(keyValue: (A, B)): ListMap[A, B] = {
    ListSpecs.filterMapNotIn(toList, keyValue._1) // gives us:
    assert(!toList.filter(_._1 != keyValue._1).map(_._1).contains(keyValue._1))

    ListSpecs.noDuplicateMapFilter(toList, (kv: (A, B)) => kv._1 != keyValue._1, (kv: (A, B)) => kv._1) // gives us:
    assert(ListSpecs.noDuplicate(toList.filter(_._1 != keyValue._1).map(_._1)))

    ListMap(keyValue :: toList.filter(_._1 != keyValue._1))
  }.ensuring(res => res.contains(keyValue._1) && res(keyValue._1) == keyValue._2)

  def ++(keyValues: List[(A, B)]): ListMap[A, B] = {
    decreases(keyValues)
    keyValues match {
      case Nil()                => this
      case Cons(keyValue, rest) => (this + keyValue) ++ rest
    }
  }

  def -(key: A): ListMap[A, B] = {
    if (contains(key)) {
      ListSpecs.noDuplicateMapFilter(toList, (kv: (A, B)) => kv._1 != key, (kv: (A, B)) => kv._1)
      ListMap(toList.filter(_._1 != key))
    } else {
      this
    }
  }

  def --(keys: List[A]): ListMap[A, B] = keys match {
    case Nil()           => this
    case Cons(key, rest) => (this - key) -- rest
  }

  def forall(p: ((A, B)) => Boolean): Boolean = {
    toList.forall(p)
  }

  def updated(a: A, b: B): ListMap[A, B] = this + (a -> b)

  def values: List[B] = toList.map(_._2)

  def keys: List[A] = toList.map(_._1)

  def map[A2, B2](f: ((A, B)) => (A2, B2)): ListMap[A2, B2] = {
    def rec(curr: List[(A, B)], acc: ListMap[A2, B2]): ListMap[A2, B2] = curr match {
      case Nil() => acc
      case Cons(h, tl) => rec(tl, acc + f(h))
    }
    rec(toList, ListMap.empty)
  }

  def filter(p: ((A, B)) => Boolean): ListMap[A, B] = {
    ListSpecs.filterSubseq(toList, p)
    ListMapLemmas.noDuplicatePairs(this)
    ListSpecs.noDuplicateSubseq(toList.filter(p), toList)
    ListMapLemmas.noDuplicateKeysSubseq(toList.filter(p), toList)
    ListMap(toList.filter(p))
  }

  def size: BigInt = toList.size
}

@library
object ListMap {
  @library
  def empty[A, B]: ListMap[A, B] = ListMap(List.empty[(A, B)])

  @library
  def fromList[K, V](l: List[(K, V)]): ListMap[K, V] = l.foldLeft(ListMap.empty[K, V]) {
    case (current, (k, v)) => current + (k -> v)
  }

  @library
  implicit class ToListMapOps[K, V](l: List[(K, V)]) {
    def toListMap: ListMap[K, V] = fromList(l)
  }
}