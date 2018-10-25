/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.lang
import stainless.annotation._

object MutableMap {
  @extern @library
  def mkString[A, B](map: MutableMap[A, B], inkv: String, betweenkv: String, fA : A => String, fB: B => String) = {
    map.theMap.map{ case (k, v) => fA(k) + inkv + fB(v)}.toList.sorted.mkString(betweenkv)
  }

  @ignore
  def withDefaultValue[A,B](default: () => B) =
    MutableMap[A,B](scala.collection.mutable.Map[A,B](), default)
}

@ignore
case class MutableMap[A, B] (theMap: scala.collection.mutable.Map[A,B], default: () => B) {
  def apply(k: A): B = if (theMap.contains(k)) {
    theMap(k)
  } else {
    default()
  }

  def update(k: A, v: B): Unit = {
    theMap(k) = v
  }
}
