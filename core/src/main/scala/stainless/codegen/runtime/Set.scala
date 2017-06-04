/* Copyright 2009-2016 EPFL, Lausanne */

package stainless.codegen.runtime

import scala.collection.mutable.{Set => MutableSet}

final class Set private(private val underlying: MutableSet[AnyRef]) {
  def this() = this(MutableSet.empty[AnyRef])
  def this(elements: Array[AnyRef]) = this(MutableSet.empty ++ elements)

  // Uses mutation! Useful at building time.
  def insert(elem: AnyRef): Unit = underlying += elem

  def getElements: Iterable[AnyRef] = underlying

  def contains(elem: AnyRef): Boolean = underlying.contains(elem)

  def add(elem: AnyRef): Set = {
    val ns = new Set(underlying.clone)
    ns.insert(elem)
    ns
  }

  def subsetOf(that: Set): Boolean = underlying.subsetOf(that.underlying)

  def union(that: Set): Set = new Set(underlying ++ that.underlying)

  def intersect(that: Set): Set = new Set(underlying intersect that.underlying)

  def difference(that: Set): Set = new Set(underlying -- that.underlying)

  override def equals(that: Any): Boolean = that match {
    case s: Set => underlying.toSet == s.underlying.toSet // the conversion to Set is mandatory!
    // Depending on how the Set was created, the underlying datastruct can be an Array and Array.equals doesn't work as one expect.
    case _ => false
  }

  override def hashCode: Int = underlying.hashCode

  override def toString: String = underlying.mkString("Set(", ", ", ")")
}
