/* Copyright 2009-2021 EPFL, Lausanne */

package stainless.ast

trait Types extends inox.ast.Types { self: Trees =>

  sealed case class ArrayType(base: Type) extends Type

  protected def getArrayType(tpe: Typed, tpes: Typed*)(using Symbols): Type = tpe.getType match {
    case at: ArrayType => checkAllTypes(tpes, at, at)
    case _ => Untyped
  }
}
