/* Copyright 2009-2024 EPFL, Lausanne */

import stainless.lang._

object MayHeapify:

  val MAX = 100000

  def maxHeapifyM(a: Array[Int], N: Int, i: Int): Unit =
    require(i >= 0 && i < N && N <= a.length && N <= MAX)
    decreases(N - i)
    val l = leftM(i)
    val r = rightM(i)
    val largest =
      if l < N && a(l) > a(i) then
        l
      else
        i
    val largest2 =
      if r < N && a(r) > a(largest) then
        r
      else
        largest
    if largest2 != i then
        val temp = a(i)
        a(i) = a(largest2)
        a(largest2) = temp
        maxHeapifyM(a, N, largest2)

  def leftM(i: Int) : Int =
    require(0 <= i && i < MAX)
    2 * i + 1

  def rightM(i: Int) : Int =
    require(0 <= i && i < MAX)
    2 * i + 2


  def maxHeapify(a: Array[Int], N: Int, i: Int): Unit =
    require(i >= 0 && i < N && N <= a.length && N <= MAX)
    decreases(N - i)
    val l = 2 * i + 1
    val r = 2 * i + 2
    val largest =
      if l < N && a(l) > a(i) then
        l
      else
        i
    val largest2 =
      if r < N && a(r) > a(largest) then
        r
      else
        largest
    if largest2 != i then
      swap(i, largest2, a, N)
      maxHeapify(a, N, largest2)

  def swap(a: Int, b: Int, array: Array[Int], N: Int): Unit =
    require(a >= 0 && a < N && b >= 0 && b < N && N <= array.length && N <= MAX)
    val temp = array(a)
    array(a) = array(b)
    array(b) = temp
