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
  @inline val `0`: Nat = Nat(0)
  @inline val `1`: Nat = Nat(1)
  @inline val `2`: Nat = Nat(2)
}

