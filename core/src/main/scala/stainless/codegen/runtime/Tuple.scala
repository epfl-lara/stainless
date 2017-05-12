/* Copyright 2009-2016 EPFL, Lausanne */

package stainless.codegen.runtime

import java.util.Arrays

final class Tuple (_elems: Array[AnyRef]) {
  private val elements = Arrays.copyOf(_elems, _elems.length)

  private var __read = 0

  def __getRead(): Int = __read

  def get(i: Int): AnyRef = {
    if (i < 0 || i >= elements.length)
      throw new IllegalArgumentException("Invalid tuple index : " + i)

    __read = (1 << i) | __read

    elements(i)
  }

  def getArity(): Int = elements.length

  override def equals(that: Any): Boolean = that match {
    case tpl: Tuple => elements.toSeq == tpl.elements.toSeq // the conversion to Seq is mandatory! Array.equals doesn't work as one expect.
    case _ => false
  }

  override def hashCode: Int = elements.toSeq.hashCode

  override def toString: String = elements.toSeq.mkString("(", ", ", ")")
}
