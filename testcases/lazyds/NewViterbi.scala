package withOrb

import leon._
import mem._
import lang._
import annotation._
import instrumentation._
import invariant._
import collection._
import math._


/**
 * Implementation of the Viterbi algorithm
 * Wiki - https://en.wikipedia.org/wiki/Viterbi_algorithm
 * The probabilities are in logarithms.
 */
object Viterbi {

  @ignore
  var xstring = Array[BigInt]()
  @ignore
  var ystring = Array[BigInt]()
  /**
   * Observation space, O
   */
  @extern
  def O(i: BigInt) = {
    xstring(i.toInt)
  } ensuring (_ => steps <= 1)
  /**
   * State space, S
   */
  @extern
  def S(i: BigInt) = {
    xstring(i.toInt)
  } ensuring (_ => steps <= 1)
  /**
   * Let K be the size of the state space. Then the transition matrix
   * A of size K * K such that A_{ij} stores the transition probability
   * of transiting from state s_i to state s_j
   */
  @extern
  def A(i: BigInt, j: BigInt) = {
    xstring(i.toInt)
  } ensuring (_ => steps <= 1)
  /**
   * Let N be the size of the observation space. Emission matrix B of
   * size K * N such that B_{ij} stores the probability of observing o_j
   * from state s_i
   */
  @extern
  def B(i: BigInt, j: BigInt) = {
    xstring(i.toInt)
  } ensuring (_ => steps <= 1)
  /**
   * An array of initial probabilities C of size K such that C_i stores
   * the probability that x_1 == s_i
   */
  @extern
  def C(i: BigInt) = {
    xstring(i.toInt)
  } ensuring (_ => steps <= 1)
  /**
   * Generated observations, Y
   */
  @extern
  def Y(i: BigInt) = {
    xstring(i.toInt)
  } ensuring (_ => steps <= 1)

  def deps(j: BigInt, K: BigInt): Boolean = {
    require(j >= 0 && K >= 0)
    if (j <= 0) true
    else columnsCachedfrom(j - 1, K)
  }

  def columnsCachedfrom(j: BigInt, K: BigInt): Boolean = {
    require(j >= 0 && K >= 0)
    columnCached(K, j, K) && {
      if (j <= 0) true
      else columnsCachedfrom(j - 1, K)
    }
  }

  def columnCached(i: BigInt, j: BigInt, K: BigInt): Boolean = {
    require(i >= 0 && j >= 0 && K >= i)
    cached(viterbi(i, j, K)) && {
      if (i <= 0) true
      else columnCached(i - 1, j, K)
    }
  }

  @traceInduct
  def columnMono(i: BigInt, j: BigInt, K: BigInt, st1: Set[Fun[BigInt]], st2: Set[Fun[BigInt]]) = {
    require(i >= 0 && j >= 0 && K >= i)
    (st1.subsetOf(st2) && (columnCached(i, j, K) in st1)) ==> (columnCached(i, j, K) in st2)
  } holds

  @traceInduct
  def columnLem(j: BigInt, K: BigInt): Boolean = {
    require(j >= 0 && K >= 0)
    if (j <= 0) (columnCached(K, j, K)) ==> (columnsCachedfrom(j, K))
    else (columnsCachedfrom(j - 1, K) && columnCached(K, j, K)) ==> (columnsCachedfrom(j, K))
  } holds

  def cachedLem(l: BigInt, j: BigInt, K: BigInt): Boolean = {
    require(j >= 0 && l >= 0 && K >= l)
    // inner function that implements the induction strategy
    @invisibleBody
    def cachedLemInduct(l: BigInt, j: BigInt, varK: BigInt, K: BigInt): Boolean = {
      require(j >= 0 && l >= 0 && varK >= l && K >= varK)
      (if (l == varK) true
      else cachedLemInduct(l, j, varK - 1, K)) &&
        (columnCached(varK, j, K) ==> columnCached(l, j, K))
    } holds

    cachedLemInduct(l, j, K, K) && (columnCached(K, j, K) ==> columnCached(l, j, K))
  }

  def columnsCachedfromMono(j: BigInt, K: BigInt, st1: Set[Fun[BigInt]], st2: Set[Fun[BigInt]]): Boolean = {
    require(j >= 0 && K >= 0)
    (columnMono(K, j, K, st1, st2) && (j <= 0 || columnsCachedfromMono(j - 1, K, st1, st2))) &&
      ((st1.subsetOf(st2) && (columnsCachedfrom(j, K) in st1)) ==> (columnsCachedfrom(j, K) in st2))
  } holds

  @invstate
  def fillEntry(l: BigInt, i: BigInt, j: BigInt, K: BigInt): BigInt = {
    decreases((abs(j), abs(K - l)))
    require(i >= 0 && j >= 1 && l >= 0 && K >= l && K >= i && deps(j, K) && cachedLem(l, j - 1, K))
    val a1 = viterbi(l, j - 1, K) + A(l, i) + B(i, Y(j))
    if (l == K) a1
    else {
      val a2 = fillEntry(l + 1, i, j, K)
      if (a1 > a2) a1 else a2
    }
  } ensuring (steps <= ? * (K - l) + ?)

  @invstate
  @memoize
  def viterbi(i: BigInt, j: BigInt, K: BigInt): BigInt = {
    require(i >= 0 && j >= 0 && K >= i && deps(j, K))
    if (j == 0) {
      C(i) + B(i, Y(0))
    } else {
      fillEntry(0, i, j, K)
    }
  } ensuring (steps <= ? * K + ?)

  def invoke(i: BigInt, j: BigInt, K: BigInt): BigInt = {
    require(i >= 0 && j >= 0 && K >= i && deps(j, K) && (i == 0 || i > 0 && columnCached(i - 1, j, K)))
    viterbi(i, j, K)
  } ensuring (res => {
    val in = inSt[BigInt]
    val out = outSt[BigInt]
    (j == 0 || columnsCachedfromMono(j - 1, K, in, out)) && columnsCachedfromMono(j, K, in, out) &&
      (i == 0 || columnMono(i - 1, j, K, in, out)) && columnCached(i, j, K) &&
      steps <= ? * K + ?
  })

  def fillColumn(i: BigInt, j: BigInt, K: BigInt): List[BigInt] = {
    decreases(abs(K - i))
    require(i >= 0 && j >= 0 && K >= i && deps(j, K) && (i == 0 || i > 0 && columnCached(i - 1, j, K)))
    if (i == K) {
      val x = invoke(i, j, K)
      Cons(x, Nil[BigInt]())
    } else {
      val x = invoke(i, j, K)
      val tail = fillColumn(i + 1, j, K)
      Cons(x, tail)
    }
  } ensuring (res => {
    columnLem(j, K) &&
      deps(j + 1, K) &&
      steps <= ? * ((K - i) * K) + ? * K + ?
  })

  @invisibleBody
  def fillTable(j: BigInt, T: BigInt, K: BigInt): List[List[BigInt]] = {
    decreases(abs(T - j))
    require(j >= 0 && T >= j && K >= 0 && deps(j, K))
    if (j == T) {
      Cons(fillColumn(0, j, K), Nil[List[BigInt]]())
    } else {
      val x = fillColumn(0, j, K)
      val tail = fillTable(j + 1, T, K)
      Cons(x, tail)
    }
  } ensuring (res => deps(T + 1, K) && steps <= ? * ((K * K) * (T - j)) + ? * ((T - j) * K) + ? * (T - j) + ? * (K * K) + ? * K + ?)

  def viterbiSols(T: BigInt, K: BigInt): List[List[BigInt]] = {
    require(T >= 0 && K >= 0)
    fillTable(0, T, K)
  } ensuring (res => deps(T + 1, K) && steps <= ? * ((K * K) * T) + ? * ((T) * K) + ? * T + ? * (K * K) + ? * K + ?)

}
