/* Copyright 2009-2016 EPFL, Lausanne */

package stainless.codegen.runtime

trait ADT {
  def __getRead(): Int

  def productElements(): Array[AnyRef]

  def productName(): String
}
