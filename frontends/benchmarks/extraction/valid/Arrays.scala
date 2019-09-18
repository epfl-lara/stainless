/* Copyright 2009-2019 EPFL, Lausanne */

import stainless.lang._

object Arrays {

  def len[T](a: Array[T]): Boolean = {
    a.length == a.size
  }.holds

  def update[T](a: Array[T], i: Int, t: T) = {
    require(i >= 0 && i < a.length)
    val array: Array[Int] = Array(0, 1)
    array(0) = 1
    // Shadowed implicit conversion not supported.
    // (array: scala.collection.mutable.ArrayOps[Int]).update(1, 2)
    a.update(i, t)
  }


  // ArraySeq not supported.
  /*
   * import scala.collection.mutable.ArraySeq
   * def updated[T](a: Array[T], i: Int, t: T): ArraySeq[T] = {
   *   require(i >= 0 && i < a.length)
   *   a.updated(i, t)
   * }
   */

  // ClassTag not supported.
  /*
   * import scala.reflect.ClassTag
   * def updated[T](a: Array[T], i: Int, u: T)(implicit m: ClassTag[T]): Array[T] = {
   *   require(i >= 0 && i < a.length)
   *   a.updated(i, u)
   * }
   */

  def updated(a: Array[Int], i: Int, v: Int): Array[Int] = {
    require(i >= 0 && i < a.length)
    a.updated(i, v)
  }

  def select[T](a: Array[T], i: Int) = {
    require(i >= 0 && i < a.length)
    a(i)
  }

}

