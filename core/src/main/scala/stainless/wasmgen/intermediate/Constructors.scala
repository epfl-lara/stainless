/* Copyright 2009-2019 EPFL, Lausanne */

package stainless.wasmgen.intermediate

trait Constructors extends stainless.ast.Constructors { self: Trees =>
  def sequence(es: Seq[Expr]): Expr = es match {
    case Seq() => UnitLiteral()
    case Seq(elem) => elem
    case more => Sequence(more)
  }
}
