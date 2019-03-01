/* Copyright 2009-2018 EPFL, Lausanne */

import stainless._
import lang._
import annotation._
import math._
import collection._

/**
 * Implementation of the Viterbi algorithm
 * Wiki - https://en.wikipedia.org/wiki/Viterbi_algorithm
 * The probabilities are in logarithms.
 */
object Viterbi {

  @extern
  def xstring = Array[BigInt]()
  @extern
  def ystring = Array[BigInt]()
  /**
   * Observation space, O
   */
  @extern
  def O(i: BigInt) = {
    xstring(i.toInt)
  }
  /**
   * State space, S
   */
  @extern
  def S(i: BigInt) = {
    xstring(i.toInt)
  }
  /**
   * Let K be the size of the state space. Then the transition matrix
   * A of size K * K such that A_{ij} stores the transition probability
   * of transiting from state s_i to state s_j
   */
  @extern
  def A(i: BigInt, j: BigInt) = {
    xstring(i.toInt)
  }
  /**
   * Let N be the size of the observation space. Emission matrix B of
   * size K * N such that B_{ij} stores the probability of observing o_j
   * from state s_i
   */
  @extern
  def B(i: BigInt, j: BigInt) = {
    xstring(i.toInt)
  }
  /**
   * An array of initial probabilities C of size K such that C_i stores
   * the probability that x_1 == s_i
   */
  @extern
  def C(i: BigInt) = {
    xstring(i.toInt)
  }
  /**
   * Generated observations, Y
   */
  @extern
  def Y(i: BigInt) = {
    xstring(i.toInt)
  }

  def fillEntry(l: BigInt, i: BigInt, j: BigInt, K: BigInt): BigInt = {
    require(i >= 0 && j >= 1 && l >= 0 && K >= l && K >= i)
    decreases(abs(j), abs(K - l))

    val a1 = viterbi(l, j - 1, K) + A(l, i) + B(i, Y(j))
    if (l == K) a1
    else {
      val a2 = fillEntry(l + 1, i, j, K)
      if (a1 > a2) a1 else a2
    }
  }

  def viterbi(i: BigInt, j: BigInt, K: BigInt): BigInt = {
    require(i >= 0 && j >= 0 && K >= i)
    if (j == 0) {
      C(i) + B(i, Y(0))
    } else {
      fillEntry(0, i, j, K)
    }
  }

  def fillColumn(i: BigInt, j: BigInt, K: BigInt): List[BigInt] = {
    require(i >= 0 && j >= 0 && K >= i)
    decreases(abs(K - i))
    if (i == K) {
      val x =  viterbi(i, j, K)
      Cons(x, Nil[BigInt]())
    } else {
      val x =  viterbi(i, j, K)
      val tail = fillColumn(i + 1, j, K)
      Cons(x, tail)
    }
  }

  def fillTable(j: BigInt, T: BigInt, K: BigInt): List[List[BigInt]] = {
    require(j >= 0 && T >= j && K >= 0)
    decreases(abs(T - j))
    if (j == T) {
      Cons(fillColumn(0, j, K), Nil[List[BigInt]]())
    } else {
      val x = fillColumn(0, j, K)
      val tail = fillTable(j + 1, T, K)
      Cons(x, tail)
    }
  }

  def viterbiSols(T: BigInt, K: BigInt): List[List[BigInt]] = {
    require(T >= 0 && K >= 0)
    fillTable(0, T, K)
  }

}
