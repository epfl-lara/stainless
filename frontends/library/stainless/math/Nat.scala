/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package math

import stainless.annotation._

@library
final case class Nat(toBigInt: BigInt) { n =>
  require(toBigInt >= 0)

  def +(m: Nat): Nat = Nat(n.toBigInt + m.toBigInt)
  def *(m: Nat): Nat = Nat(n.toBigInt * m.toBigInt)

  def -(m: Nat): Nat = {
    require(n.toBigInt - m.toBigInt >= 0)
    Nat(n.toBigInt - m.toBigInt)
  }

  def /(m: Nat): Nat = {
    require(m.isNonZero && n.toBigInt / m.toBigInt > 0)
    Nat(n.toBigInt / m.toBigInt)
  }

  def %(m: Nat): Nat = {
    require(m.isNonZero)
    Nat(n.toBigInt % m.toBigInt)
  }

  def > (m: Nat): Boolean = n.toBigInt >  m.toBigInt
  def >=(m: Nat): Boolean = n.toBigInt >= m.toBigInt
  def < (m: Nat): Boolean = n.toBigInt <  m.toBigInt
  def <=(m: Nat): Boolean = n.toBigInt <= m.toBigInt

  def mod(m: Nat): Nat = {
    require(m.isNonZero && n.toBigInt.mod(m.toBigInt) > 0)
    Nat(n.toBigInt mod m.toBigInt)
  }

  def isNonZero: Boolean = toBigInt != 0
  def isZero: Boolean    = toBigInt == 0
}

@library
object Nat {
  val `0` : Nat = Nat(0)
  val `1` : Nat = Nat(1)
  val `2` : Nat = Nat(2)
  val `3` : Nat = Nat(3)
  val `4` : Nat = Nat(4)
  val `5` : Nat = Nat(5)
  val `6` : Nat = Nat(6)
  val `7` : Nat = Nat(7)
  val `8` : Nat = Nat(8)
  val `9` : Nat = Nat(9)
  val `10`: Nat = Nat(10)
}

