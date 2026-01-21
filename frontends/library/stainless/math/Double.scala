package stainless
package math

import lang.StaticChecks._
import annotation._

@library
case class Double(@extern @pure private val value: scala.Double) extends AnyVal

@library
object Double {
  @extern @pure
  def longBitsToDouble(l: Long): Double = {
    Double(java.lang.Double.longBitsToDouble(l))
  }

  @extern @pure
  def longBitsToDoublePost(l: Long): Unit = {
    ()
  } ensuring (_ => doubleToRawLongBits(longBitsToDouble(l)) == l)

  @extern @pure
  def doubleToRawLongBits(d: Double): Long = {
    java.lang.Double.doubleToRawLongBits(d.value)
  } ensuring (res => longBitsToDouble(res) == d)
}