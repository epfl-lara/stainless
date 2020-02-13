/* Copyright 2009-2019 EPFL, Lausanne */

package stainless.codegen.runtime

import scala.collection.mutable.{Map => MutableMap}

final class Map(private val underlying: MutableMap[AnyRef, AnyRef], val default: AnyRef) {
  def this(default: AnyRef) = this(MutableMap.empty, default)

  // Uses mutation! Useful at building time.
  def insert(key: AnyRef, value: AnyRef): Unit = underlying += key -> value

  def getElements: Iterable[(AnyRef, AnyRef)] = underlying

  def get(key: AnyRef): AnyRef = underlying.getOrElse(key, default)

  def updated(key: AnyRef, value: AnyRef): Map = {
    val nm = new Map(underlying.clone, default)
    nm.insert(key, value)
    nm
  }

  override def equals(that: Any): Boolean = that match {
    case m: Map => underlying == m.underlying && default == m.default
    case _ => false
  }

  override def hashCode: Int = underlying.hashCode ^ default.hashCode

  override def toString: String = underlying.mkString("Map(", ", ", "* -> " + default + ")")
}
