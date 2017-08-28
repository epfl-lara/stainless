/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package ast

trait Constructors extends inox.ast.Constructors { self: Trees =>

  def annotated(e: Expr, flag: Flag): Expr = e match {
    case Annotated(body, flags) => Annotated(body, (flags :+ flag).distinct).copiedFrom(e)
    case _ => Annotated(e, Seq(flag)).copiedFrom(e)
  }
}
