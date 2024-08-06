package stainless
package math

import lang.StaticChecks._
import annotation._

@library
case class Float(@extern @pure private val value: scala.Float) extends AnyVal

@library
object Float {
  @extern @pure
  def intBitsToFloat(i: Int): Float = {
    Float(java.lang.Float.intBitsToFloat(i))
  }

  @extern @pure
  def intBitsToFloatPost(i: Int): Unit = {
    ()
  } ensuring (_ => floatToRawIntBits(intBitsToFloat(i)) == i)

  @extern @pure
  def floatToRawIntBits(d: Float): Int = {
    java.lang.Float.floatToRawIntBits(d.value)
  } ensuring (res => intBitsToFloat(res) == d)
}