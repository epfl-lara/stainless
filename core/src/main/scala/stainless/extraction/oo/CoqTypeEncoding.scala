/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package extraction
package oo

import scala.collection.mutable.{Map => MutableMap}

trait CoqTypeEncoding extends inox.ast.SymbolTransformer { self =>
  val s: Trees
  val t: Trees

  object transformer extends TreeTransformer {
    val s: self.s.type = self.s
    val t: self.t.type = self.t

    override def transform(e: s.Expr): t.Expr = e match {
      case s.IsInstanceOf(expr, tpe) => t.BooleanLiteral(true)
      case s.AsInstanceOf(expr,tpe) => transform(expr)
      case _ => super.transform(e)
    }
  }

  def transform(syms: s.Symbols): t.Symbols = syms.transform(transformer)
}
