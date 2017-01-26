/* Copyright 2009-2016 EPFL, Lausanne */

package stainless.codegen.runtime

import scala.collection.mutable.{Map => MutableMap}

final class Bag private(private val underlying: MutableMap[AnyRef, BigInt]) {
  def this() = this(MutableMap.empty)

  // Use mutation! Useful at building time.
  def insert(key: AnyRef): Unit = add(key, BigInt.ONE)
  def insert(key: AnyRef, count: BigInt): Unit = {
    underlying += key -> (get(key).add(count))
  }

  def getElements(): Iterable[(AnyRef, BigInt)] = underlying

  def get(key: AnyRef): BigInt = underlying.getOrElse(key, BigInt.ZERO)

  def add(key: AnyRef): Bag = {
    val nb = new Bag(underlying.clone)
    nb.insert(key)
    nb
  }

  def union(that: Bag): Bag =
    new Bag(MutableMap.empty ++ (underlying.keySet ++ that.underlying.keySet).map {
      k => k -> (get(k).add(that.get(k)))
    })

  def intersect(that: Bag): Bag =
    new Bag(MutableMap.empty ++ (underlying.keySet intersect that.underlying.keySet).map {
      key => key -> underlying(key).add(that.underlying(key))
    })
  

  def difference(that: Bag): Bag =
    new Bag(MutableMap.empty ++ underlying.toSeq.flatMap { case (key, value) =>
      val diff = value.sub(that.get(key))
      if (diff.greaterThan(BigInt.ZERO)) Some(key -> diff) else None
    })

  override def equals(that: Any): Boolean = that match {
    case b: Bag => underlying == b.underlying
    case _ => false
  }

  override def hashCode: Int = underlying.hashCode

  override def toString: String = underlying.map(p => p._1 + " -> " + p._2).mkString("Bag(", ", ", ")")
}
