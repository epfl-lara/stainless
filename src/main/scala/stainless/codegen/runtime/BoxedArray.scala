/* Copyright 2009-2016 EPFL, Lausanne */

package stainless.codegen.runtime

sealed abstract class Box { val array: Array[_] }
case class IntBox(array: Array[Int]) extends Box
case class BooleanBox(array: Array[Boolean]) extends Box
case class AnyRefBox(array: Array[AnyRef]) extends Box

final class BoxedArray private(private val box: Box) {
  def this(intArray: Array[Int]) = this(IntBox(intArray))
  def this(boolArray: Array[Boolean]) = this(BooleanBox(boolArray))
  def this(objArray: Array[AnyRef]) = this(AnyRefBox(objArray))

  def intArray(): Array[Int] = box match {
    case IntBox(array) => array
    case _ => throw new CodeGenRuntimeException("Expected integer BoxedArray")
  }

  def booleanArray(): Array[Boolean] = box match {
    case BooleanBox(array) => array
    case _ => throw new CodeGenRuntimeException("Expected boolean BoxedArray")
  }

  def anyRefArray(): Array[AnyRef] = box match {
    case AnyRefBox(array) => array
    case _ => throw new CodeGenRuntimeException("Expected anyRef BoxedArray")
  }

  override def equals(that: Any): Boolean = that match {
    case b: BoxedArray => box == b.box
    case _ => false
  }

  override def hashCode: Int = box.hashCode

  override def toString: String = box.array.toString
}

