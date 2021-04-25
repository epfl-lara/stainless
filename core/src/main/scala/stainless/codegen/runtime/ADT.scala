/* Copyright 2009-2021 EPFL, Lausanne */

package stainless.codegen.runtime

trait ADT {
  def __getRead(): Int

  def productElements(): Array[AnyRef]

  def productName(): String
}
