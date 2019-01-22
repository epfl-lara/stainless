/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.lang

import scala.language.implicitConversions

import stainless.annotation._

object Map {
  @library @inline
  @isabelle.function(term = "Map.empty")
  def empty[A,B] = Map[A,B]()

  @ignore
  def apply[A,B](elems: (A,B)*) = {
    new Map[A,B](scala.collection.immutable.Map[A,B](elems : _*))
  }
  
  @extern @library
  def mkString[A, B](map: Map[A, B], inkv: String, betweenkv: String, fA : A => String, fB: B => String) = {
    map.theMap.map{ case (k, v) => fA(k) + inkv + fB(v)}.toList.sorted.mkString(betweenkv)
  }
}

@ignore
case class Map[A, B] (theMap: scala.collection.immutable.Map[A,B]) {
  def apply(k: A): B = theMap.apply(k)
  def ++(b: Map[A, B]): Map[A,B] = new Map (theMap ++ b.theMap)
  def updated(k: A, v: B): Map[A,B] = new Map(theMap.updated(k, v))
  def contains(a: A): Boolean = theMap.contains(a)
  def isDefinedAt(a: A): Boolean = contains(a)

  def +(kv: (A, B)): Map[A,B] = updated(kv._1, kv._2)
  def +(k: A, v: B): Map[A,B] = updated(k, v)

  def getOrElse(k: A, default: B): B = get(k).getOrElse(default)

  def get(k: A): Option[B] = if (contains(k)) {
    Some[B](apply(k))
  } else {
    None[B]()
  }
}
