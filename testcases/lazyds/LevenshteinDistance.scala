package withOrb

import leon._
import mem._
import lang._
import annotation._
import instrumentation._
import invariant._
import collection._

object LevenshteinDistance {

  @ignore
  var xstring = Array[BigInt]()
  @ignore
  var ystring = Array[BigInt]()
  @extern
  def lookup(i: BigInt, j: BigInt) = {
    (xstring(i.toInt), ystring(j.toInt))
  } ensuring (_ => steps <= 1)

  // deps and it's lemmas
  def deps(i: BigInt, j: BigInt): Boolean = {
    require(i >= 0 && j >= 0)
    cached(levDist(i, j)) &&
      (if (i <= 0 && j <= 0) true
      else if (i <= 0) deps(i, j - 1)
      else if (j <= 0) deps(i - 1, j)
      else deps(i - 1, j) && deps(i, j - 1))
  }

  @invisibleBody
  @traceInduct
  def depsMono(i: BigInt, j: BigInt, st1: Set[Fun[BigInt]], st2: Set[Fun[BigInt]]) = {
    require(i >= 0 && j >= 0)
    (st1.subsetOf(st2) && (deps(i, j) in st1)) ==> (deps(i, j) in st2)
  } holds

  @traceInduct
  def depsLem(i: BigInt, j: BigInt, m: BigInt, n: BigInt) = {
    require(i >= 0 && j >= 0 && m >= 0 && n >= 0)
    (i <= m && j <= n && deps(m, n)) ==> deps(i, j)
  } holds

  @invstate
  @memoize
  @invisibleBody
  def levDist(i: BigInt, j: BigInt): BigInt = {
    require((i >=0 && j >= 0) && (i == 0 || deps(i - 1, j)) && (j == 0 || deps(i, j-1)))
    if (i == 0) j
    else if(j == 0) i
    else {
      val (xi, yj) = lookup(i, j)
      val dprev = levDist(i - 1, j - 1)
      val a1 = if (xi == yj) dprev else dprev + 1
      val a2 = {
        val s1 = levDist(i - 1, j)
        val s2 = levDist(i, j - 1)
        if (s1 >= s2) s1 else s2
      }
      if (a1 >= a2) a1 else a2
    }
  } ensuring (_ => steps <= ?)

  @invisibleBody
  def invoke(i: BigInt, j: BigInt, n: BigInt) = {
    require((i >=0 && j >= 0 && n >= j) && (i == 0 || deps(i - 1, j)) && (j == 0 || deps(i, j-1)))
    levDist(i, j)
  } ensuring (res => {
    val in = inSt[BigInt]
    val out = outSt[BigInt]
      (i == 0 || (depsMono(i - 1, j, in, out) && depsMono(i - 1, n, in, out))) &&
      (j == 0 || depsMono(i, j - 1, in, out)) &&
      deps(i, j) &&
      steps <= ?
  })

  /**
  * Same as LCS, look at that file for more insights
  */
  def bottomup(m: BigInt, j: BigInt, n: BigInt): List[BigInt] = {
    require(0 <= m && 0 <= j && j <= n)
    if (m == 0 && j == 0) {
      Cons(invoke(m, j, n), Nil[BigInt]())
    }
    else if(j == 0) {
      val tail = bottomup(m - 1, n, n)
      Cons(invoke(m, j, n), tail)
    }
    else {
      val tail = bottomup(m, j - 1, n)
      Cons(invoke(m, j, n), tail)
    }
  } ensuring {_ =>
    bottomUpPost(m, j, n) &&
      steps <= ? * (m * n)  + ? * m + ? * j + ?
   }

  @invisibleBody
  def bottomUpPost(m: BigInt, j: BigInt, n: BigInt): Boolean = {
    require(m >= 0 && n >= j && j >= 0)
    (m == 0 || (deps(m - 1, n) && (j == n || depsLem(m - 1, j + 1, m - 1, n)))) && deps(m, j) &&
      depsLem(m, 0, m, j)
  }

  def levDistSols(m: BigInt, n: BigInt): List[BigInt] = {
    require(0 <= m && 0 <= n)
    bottomup(m, n, n)
  } ensuring(_ => steps <= ? * (m * n)  + ? * m + ? * n + ?)
}
