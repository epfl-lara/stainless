/* Copyright 2009-2021 EPFL, Lausanne */

package stainless.lang

import scala.collection.immutable.{Map => ScalaMap}

import StaticChecks._
import stainless.annotation._
import stainless.collection.List
import stainless.collection.ListMap
import stainless.collection.TupleListOpsGenK

object Map {
  @library @inline
  @isabelle.function(term = "Map.empty")
  def empty[A,B] (using CanEqual[A, A])= Map[A,B]()

  @ignore
  def apply[A,B](elems: (A,B)*)(using CanEqual[A, A]) = {
    new Map[A,B](scala.collection.immutable.Map[A,B](elems*))
  }

  @library @extern @pure
  def fromScala[A, B](map: ScalaMap[A, B]): Map[A, B] = {
    new Map(map)
  }

  @library @extern @pure
  def mkString[A, B](map: Map[A, B], innerSep: String, outerSep: String)(fA: A => String, fB: B => String): String = {
    map.theMap
      .map { case (k, v) => fA(k) + innerSep + fB(v) }
      .toList.sorted
      .mkString(outerSep)
  }

  @library
  implicit class MapOps[A, B](val map: Map[A, B]) extends AnyVal {

    @extern @pure
    def keys: List[A] = {
      List.fromScala(map.theMap.keys.toList)
    }

    @extern @pure
    def keysPost(a: A)(using CanEqual[A, A]): Unit = {
      ()
   }.ensuring { _ =>
      map.contains(a) == keys.contains(a)
    }


    @extern @pure
    def values: List[B] = {
      List.fromScala(map.theMap.values.toList)
    }

    @extern @pure
    def valuesPost1(a: A)(using CanEqual[B, B], CanEqual[A, A]): Unit = {
      ()
   }.ensuring { _ =>
      !map.contains(a) || values.contains(map(a))
    }

    @extern @pure
    def valuesPost2(b: B)(using CanEqual[B, B], CanEqual[A, A]): A = {
      require(values.contains(b))
      (??? : A)
   }.ensuring((a:A) => b == map(a) && map.contains(a))

    @extern @pure
    def toList(using CanEqual[A, A], CanEqual[B, B]): List[(A, B)] = {
      List.fromScala(map.theMap.toList)
    }.ensuring(res => TupleListOpsGenK.noDuplicatedKeys(res))

    /**
      * This enables induction on maps.
      *
      * @return
      */
    @pure @ghost
    def toListMap(using CanEqual[A, A], CanEqual[B, B]): ListMap[A, B] = {
      ListMap(map.toList)
    }

    @extern @pure
    def toListPost(a: A)(using CanEqual[A, A], CanEqual[B, B]): Unit = {
      ()
   }.ensuring(_ => map.contains(a) ==> toList.contains((a, map(a))))

    @extern @pure
    def toScala: ScalaMap[A, B] = {
      map.theMap
    }
  }

  @library
  def fromList[K, V](l: List[(K, V)])(using CanEqual[K, K]): Map[K, V] = l.foldLeft(Map[K, V]()) {
    case (current, (k, v)) => current ++ Map(k -> v)
  }

  @library
  implicit class ToMapOps[K, V](l: List[(K, V)]) {
    def toMap(using CanEqual[K, K]): Map[K, V] = fromList(l)
  }
}

@ignore
case class Map[A, B] (theMap: scala.collection.immutable.Map[A,B]) derives CanEqual {
  def apply(k: A)(using CanEqual[A, A]): B = theMap.apply(k)
  def updated(k: A, v: B)(using CanEqual[A, A]): Map[A,B] = new Map(theMap.updated(k, v))
  def removed(k: A)(using CanEqual[A, A]): Map[A, B] = new Map(theMap - k)
  def contains(a: A)(using CanEqual[A, A]): Boolean = theMap.contains(a)
  def isDefinedAt(a: A)(using CanEqual[A, A]): Boolean = contains(a)

  def +(kv: (A, B))(using CanEqual[A, A]): Map[A,B] = updated(kv._1, kv._2)
  def +(k: A, v: B)(using CanEqual[A, A]): Map[A,B] = updated(k, v)
  def -(k: A)(using CanEqual[A, A]): Map[A, B] = removed(k)

  def ++(b: Map[A, B])(using CanEqual[A, A]): Map[A,B] = new Map(theMap ++ b.theMap)
  def --(b: Set[A])(using CanEqual[A, A]): Map[A,B] = new Map(theMap -- b.theSet)

  def getOrElse(k: A, default: B)(using CanEqual[A, A]): B = get(k).getOrElse(default)

  def get(k: A)(using CanEqual[A, A]): Option[B] = if (contains(k)) {
    Some[B](apply(k))
  } else {
    None[B]()
  }
}
