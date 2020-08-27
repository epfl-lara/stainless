/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package extraction
package utils

import java.util.concurrent.ConcurrentHashMap

class ConcurrentCache[A,B](underlying: ConcurrentHashMap[A,B] = new ConcurrentHashMap[A,B]) {
  def get(key: A): Option[B] = Option(underlying.get(key))
  def update(key: A, value: B): Unit = underlying.put(key, value)
  def getOrElseUpdate(key: A, value: => B): B = {
    if (underlying.containsKey(key)) underlying.get(key)
    else {
      val res = value
      underlying.put(key, res)
      res
    }
  }
  def contains(key: A): Boolean = underlying.containsKey(key)
  def apply(key: A): B = get(key).get

  def cached(key: A)(value: => B): B = {
    val result = underlying.get(key)
    if (result != null) result else {
      val newValue = value // force the value
      val previous = underlying.putIfAbsent(key, newValue)
      if (previous == null) newValue else previous
    }
  }

  def retain(p: A => Boolean): Unit = synchronized {
    val it = underlying.keySet.iterator
    while (it.hasNext) {
      if (!p(it.next)) it.remove
    }
  }
}

class ConcurrentCached[A,B](builder: A => B) extends (A => B) {
  private[this] val cache: ConcurrentCache[A,B] = new ConcurrentCache[A,B]
  override def apply(key: A): B = cache.cached(key)(builder(key))
}
