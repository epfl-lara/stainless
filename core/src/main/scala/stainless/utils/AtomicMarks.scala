/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package utils

/** Set of marks that are atomically set. */
class AtomicMarks[A] {

  /**
   * Atomically set the mark for [[a]].
   *
   * Returns [[true]] if the mark was **not** set before,
   * [[false]] on subsequent call for the same [[a]] until
   * a call to [[clear]].
   */
  def compareAndSet(a: A): Boolean = underlying.putIfAbsent(a, unusedValue).isEmpty

  /**
   * Clear all marks.
   */
  def clear(): Unit = underlying.clear()

  private type UnusedType = Unit
  private val unusedValue = ()
  private val underlying = scala.collection.concurrent.TrieMap[A, UnusedType]()

}

