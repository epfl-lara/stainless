/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.lang
import stainless.annotation._

object MutableMap {
  @extern @library
  def mkString[A, @mutable B](map: MutableMap[A, B], inkv: String, betweenkv: String, fA : A => String, fB: B => String) = {
    map.theMap.map{ case (k, v) => fA(k) + inkv + fB(v)}.toList.sorted.mkString(betweenkv)
  }

  @ignore
  def withDefaultValue[A, @mutable B](default: () => B) =
    MutableMap[A,B](scala.collection.mutable.Map[A,B](), default)
}

@ignore
case class MutableMap[A, @mutable B] (theMap: scala.collection.mutable.Map[A,B], default: () => B) {
  def apply(k: A): B = if (theMap.contains(k)) {
    theMap(k)
  } else {
    default()
  }

  def update(k: A, v: B): Unit = {
    theMap(k) = v
  }

  // To avoid the creation of aliases on the elements of `B`,
  // `updated` and `duplicate` can only be used when `B` is an immutable type
  def updated(k: A, v: B) = {
    MutableMap(theMap.updated(k, v), default)
  }

  def duplicate() = {
    MutableMap(theMap.clone(), default)
  }
}
