/* Copyright 2009-2019 EPFL, Lausanne */

package stainless.lang

import scala.language.implicitConversions
import scala.collection.immutable.{Map => ScalaMap}

import StaticChecks._
import stainless.annotation._
import stainless.collection.List

object Map {
  @library @inline
  @isabelle.function(term = "Map.empty")
  def empty[A,B] = Map[A,B]()

  @ignore
  def apply[A,B](elems: (A,B)*) = {
    new Map[A,B](scala.collection.immutable.Map[A,B](elems : _*))
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
    } ensuring { res =>
      forall((a: A) => map.contains(a) == res.contains(a))
    }

    @extern @pure
    def values: List[B] = {
      List.fromScala(map.theMap.values.toList)
    } ensuring { res =>
      forall((a: A, b: B) => (map.contains(a) && map(a) == b) == res.contains(b))
    }

    @extern @pure
    def toList: List[(A, B)] = {
      List.fromScala(map.theMap.toList)
    } ensuring { res =>
      forall((a: A) => map.contains(a) == res.contains((a, map(a))))
    }

    @extern @pure
    def toScala: ScalaMap[A, B] = {
      map.theMap
    }
  }
}

@ignore
case class Map[A, B] (theMap: scala.collection.immutable.Map[A,B]) {
  def apply(k: A): B = theMap.apply(k)
  def updated(k: A, v: B): Map[A,B] = new Map(theMap.updated(k, v))
  def removed(k: A): Map[A, B] = new Map(theMap - k)
  def contains(a: A): Boolean = theMap.contains(a)
  def isDefinedAt(a: A): Boolean = contains(a)

  def +(kv: (A, B)): Map[A,B] = updated(kv._1, kv._2)
  def +(k: A, v: B): Map[A,B] = updated(k, v)
  def -(k: A): Map[A, B] = removed(k)

  def ++(b: Map[A, B]): Map[A,B] = new Map(theMap ++ b.theMap)
  def --(b: Set[A]): Map[A,B] = new Map(theMap -- b.theSet)

  def getOrElse(k: A, default: B): B = get(k).getOrElse(default)

  def get(k: A): Option[B] = if (contains(k)) {
    Some[B](apply(k))
  } else {
    None[B]()
  }
}
