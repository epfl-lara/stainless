
/* Copyright 2017- LARA, EPFL, Lausanne.
   Author: Dragana Milovancevic. */
package example

import stainless.collection._
import stainless.lang._
import stainless.annotation._
import stainless.proof._

object Lists {
  /**
   * This method computes the sum of all elements in the list xs. There are
   * multiple techniques that can be used for implementing this method, and
   * you will learn during the class.
   *
   * For this example assignment you can use the following methods in class
   * `List`:
   *
   *  - `xs.isEmpty: Boolean` returns `true` if the list `xs` is empty
   *  - `xs.head: Int` returns the head element of the list `xs`. If the list
   *    is empty an exception is thrown
   *  - `xs.tail: List[Int]` returns the tail of the list `xs`, i.e. the the
   *    list `xs` without its `head` element
   *
   *  ''Hint:'' instead of writing a `for` or `while` loop, think of a recursive
   *  solution.
   *
   * @param xs A list of natural numbers
   * @return The sum of all elements in `xs`
   */
  def sum(xs: List[Int]): Int = {
    decreases(xs)
    if (xs.isEmpty) 0
    else xs.head + sum(xs.tail)
  }

  def sumInit(@induct xs: List[Int]) = {
    (xs.isEmpty && sum(xs) == 0) ||
    (sum(xs) == xs.last + sum(xs.init))
  }.holds

  /**
   * This method returns the largest element in a list of integers. If the
   * list `xs` is empty it throws a `java.util.NoSuchElementException`.
   *
   * You can use the same methods of the class `List` as mentioned above.
   *
   * ''Hint:'' Again, think of a recursive solution instead of using looping
   * constructs. You might need to define an auxiliary method.
   *
   * @param xs A list of natural numbers
   * @return The largest element in `xs`
   */
  def recmax(xs: List[Int], max:Int): Int = {
    decreases(xs)
    if (xs.isEmpty) max
    else if (max > xs.head) recmax(xs.tail, max)
    else recmax(xs.tail, xs.head)
  }

  def max(xs: List[Int]): Int = {
    require(!xs.isEmpty)

    recmax(xs.tail, xs.head)
  }

  def recmaxGreater(xs: List[Int], max1: Int, max2: Int): Boolean = {
    require(max1 >= max2)
    decreases(xs)

    if (!xs.isEmpty) {
      if (max1 > xs.head)
        if (max2 > xs.head) check(recmaxGreater(xs.tail, max1, max2))
        else check(recmaxGreater(xs.tail, max1, xs.head))
    }

    recmax(xs, max1) >= recmax(xs, max2)
  }.holds

  def maxTail(xs: List[Int]) = {
    require(!xs.isEmpty && !xs.tail.isEmpty)

    assert(max(xs) == recmax(xs.tail, xs.head))
    assert(max(xs.tail) == recmax(xs.tail.tail, xs.tail.head))

    if (xs.head > xs.tail.head)
      check(recmaxGreater(xs.tail.tail, xs.head, xs.tail.head))
    else
      check(recmaxGreater(xs.tail.tail, xs.tail.head, xs.head))

    max(xs) >= max(xs.tail)
  }.holds
}
