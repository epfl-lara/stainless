/* Copyright 2009-2024 EPFL, Lausanne */

import stainless.lang._

object SortedArray:

  def isSortedArrayM(a: Array[BigInt], start: Int, n: Int): Boolean =
    decreases(n)
    require(0 <= start && n >= start && n <= a.length)
    if n <= succM(start) then
      true
    else if a(n-2) > a(n-1) then
      false
    else
      isSortedArrayM(a, start, n-1)

  def succM(n: Int) =
    if n < Int.MaxValue then
      n + 1
    else
      n

  def isSortedArray(a: Array[BigInt], start: Int, n: Int): Boolean =
    decreases(n)
    require(0 <= start && n >= start && n <= a.length)
    if n == start then
      true
    else if n == start + 1 then
      true
    else if a(n-2) > a(n-1) then
      false
    else
      isSortedArray(a, start, n-1)
