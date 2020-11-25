/* Copyright 2009-2021 EPFL, Lausanne */

package stainless.codegen.runtime

abstract class Lambda {
  def apply(args: Array[AnyRef]): AnyRef
}
