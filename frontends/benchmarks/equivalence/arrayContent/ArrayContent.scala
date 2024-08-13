/* Copyright 2009-2024 EPFL, Lausanne */

import stainless.lang._

object ArrayContent:

  val MAX = 100000

  def arrayContentM(a: Array[BigInt], n: Int) : Set[BigInt] =
    require(n >= 0 && n <= a.length && a.length <= MAX)
    decreases(n)
    if n == 0 then Set.empty[BigInt]
    else arrayContentM(a, n-1) ++ Set(a(n-1))


  def arrayContent(a: Array[BigInt], n: Int) : Set[BigInt] =
    require(n >= 0 && n <= a.length && a.length <= MAX)
    decreases(n)
    if n == 0 then Set.empty[BigInt]
    else Set(a(n-1)) ++ arrayContent(a, n-1)
