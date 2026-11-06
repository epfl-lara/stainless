import stainless.annotation.*
import stainless.lang.*

object AnyEq:
  // Each assertion states the value of the "Stainless" column of the table

  def byteInt(): Unit =
    val a: Any = (5: Byte)
    val b: Any = 5
    assert((a == b) == false)

  def charInt(): Unit =
    val a: Any = 'a'
    val b: Any = 97
    assert((a == b) == false)

  def bigIntInt(): Unit =
    val a: Any = BigInt(5)
    val b: Any = 5
    assert((a == b) == false)

  def tuples(): Unit =
    val a: Any = (1, 2)
    val b: Any = ((1: Byte), (2: Short))
    assert((a == b) == false)

  def eq[@mutable T](x: T, y: T) = x == y

  def typeParam(): Unit = assert(eq[Any](5: Byte, 5) == false)

  case class CA(a: Any)

  def caseClassField(): Unit = assert((CA(5: Byte) == CA(5)) == false)

  def nanAny(): Unit =
    val a: Any = Double.NaN
    val b: Any = Double.NaN
    assert((a == b) == true)

  def zeroAny(): Unit =
    val a: Any = 0.0
    val b: Any = -0.0
    assert((a == b) == false)

  class P(val x: Int)
  def plainClass(): Unit = assert((new P(1) == new P(1)) == true)

  case class Q(x: Int, y: Int):
    override def equals(that: Any): Boolean = that match
      case Q(x2, _) => x == x2
      case _ => false

  def customEquals(): Unit = assert((Q(1, 2) == Q(1, 3)) == false)

  // Agreeing cases
  sealed abstract class D1
  case class C1(x: Int) extends D1
  case class E1(x: Int) extends D1

  def sameInt(): Unit =
    val a: Any = 2
    val b: Any = 2
    assert((a == b) == true)

  def siblings(): Unit =
    val a: Any = C1(1)
    val b: Any = E1(1)
    assert((a == b) == false)

  def upcast(): Unit =
    assert(((C1(1): D1) == (C1(1): C1)) == true)
