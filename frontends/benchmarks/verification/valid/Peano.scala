/* Copyright 2009-2018 EPFL, Lausanne */

import stainless.annotation._
import stainless.lang._

object Peano {
  sealed abstract class Nat
  case class Zero() extends Nat
  case class Succ(num: Nat) extends Nat

  def plus(a: Nat, b: Nat): Nat = a match {
    case Zero()   => b
    case Succ(a1) => Succ(plus(a1, b))
  }

  def nat2Int(n: Nat): Int = n match {
    case Zero() => 0
    case Succ(n1) => 1 + nat2Int(n1)
  }

  def int2Nat(n: Int): Nat = {
    require(n >= 0)
    if (n == 0) Zero() else Succ(int2Nat(n-1))
  }

  def sum_lemma(): Boolean = {
    3 == nat2Int(plus(int2Nat(1), int2Nat(2)))
  }.holds
}
