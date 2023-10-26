/* Copyright 2009-2021 EPFL, Lausanne */

package stainless.ast

trait Types extends inox.ast.Types { self: Trees =>

  sealed case class ArrayType(base: Type) extends Type
  sealed case class CellType(v: Type) extends Type

}
