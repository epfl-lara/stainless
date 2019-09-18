/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package codegen
package runtime

import scala.collection.mutable.{Map => MutableMap}

final class BigArray(private val underlying: MutableMap[Int, AnyRef], val size: Int, val default: AnyRef) {
  def this(size: Int) = this(MutableMap.empty, size, null)
  def this(size: Int, default: AnyRef) = this(MutableMap.empty, size, default)

  // Uses mutation! Useful at building time.
  def insert(index: Int, value: AnyRef): Unit = {
    if (index < 0 || index >= size) throw new CodeGenRuntimeException("Invalid array index: " + index)
    underlying += index -> value
  }

  def getElements: Iterable[(Int, AnyRef)] = underlying

  def get(index: Int): AnyRef = {
    if (index < 0 || index >= size) throw new CodeGenRuntimeException("Invalid array index: " + index)
    underlying.getOrElse(index, default)
  }

  def updated(index: Int, value: AnyRef): BigArray = {
    val arr = new BigArray(underlying.clone, size, default)
    arr.insert(index, value)
    arr
  }

  override def equals(that: Any): Boolean = that match {
    case a: BigArray => underlying == a.underlying && size == a.size && default == a.default
    case _ => false
  }

  override def hashCode: Int = {
    61 * underlying.hashCode +
    31 * size.hashCode +
    (if (default == null) 5 else default.hashCode)
  }

  override def toString: String = underlying.mkString("Array(", ", ", ") (of size " + size + " with default " + default + ")")
}
