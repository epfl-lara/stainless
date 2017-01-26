/* Copyright 2009-2016 EPFL, Lausanne */

package stainless.codegen.runtime

abstract class Lambda {
  def pre: Lambda
  def apply(args: Array[AnyRef]): AnyRef
}
