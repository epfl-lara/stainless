/* Copyright 2009-2021 EPFL, Lausanne */

// use `.updated` from Stainless library
import stainless.lang._

// unimport implicit conversions for `.updated`
import scala.Predef.{ genericArrayOps => _, genericWrapArray => _, copyArrayToImmutableIndexedSeq => _, _ }

object Arrays {

  def update[T](a: Array[T], i: Int, t: T) = {
    require(i >= 0 && i < a.length)
    val array: Array[Int] = Array(0, 1)
    array(0) = 1
    // Shadowed implicit conversion not supported.
    // (array: scala.collection.mutable.ArrayOps[Int]).update(1, 2)
    a.update(i, t)
  }

  def updated[T](a: Array[T], i: Int, t: T): Array[T] = {
    require(i >= 0 && i < a.length)

    a.updated(i, t)
  }

  def updated(a: Array[Int], i: Int, v: Int): Array[Int] = {
    require(i >= 0 && i < a.length)
    a.updated(i, v)
  }

  def select[T](a: Array[T], i: Int) = {
    require(i >= 0 && i < a.length)
    a(i)
  }

}

