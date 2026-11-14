/* Copyright 2009-2024 EPFL, Lausanne */
/* From ESOP 2014, Kuwahara et al */

import stainless.lang._

object Partial:

  def maxNegPM(j: BigInt, p: BigInt => Boolean): Boolean =
    !p(j) && forall((k: BigInt) => !p(k) ==> (k <= j))

  def fM(x: BigInt, p: BigInt => Boolean): BigInt =
    // quantifiers are propositions: the existential is stated here rather than passed around
    // as a predicate
    require(!p(x) || !forall((j: BigInt) => !(j < x && maxNegPM(j, p))))
    decreases(if (!p(x)) BigInt(0) else x - choose((j: BigInt) => j < x && maxNegPM(j, p)))
    if (p(x)) then fM(x - 1, p)
    else  x


  def maxNegP(p: BigInt => Boolean, j: BigInt): Boolean =
    if p(j) then
      false
    else
      forall((k: BigInt) => !p(k) ==> (k <= j))

  def f(x: BigInt, p: BigInt => Boolean): BigInt =
    require(!p(x) || !forall((j: BigInt) => !(j < x && maxNegP(p, j))))
    decreases(if (!p(x)) BigInt(0) else x - choose((j: BigInt) => j < x && maxNegPM(j, p)))
    val t = p(x)
    if t then f(x - 1, p)
    else x
