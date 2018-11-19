/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.ast

trait Types extends inox.ast.Types { self: Trees =>

  sealed case class ArrayType(base: Type) extends Type

}
