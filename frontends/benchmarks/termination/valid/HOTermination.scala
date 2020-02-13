/* Copyright 2009-2019 EPFL, Lausanne */

import stainless.lang._
import stainless.collection._

object HOTermination {
  sealed abstract class Expr
  case class Invocation(e: Expr, args: List[Expr]) extends Expr
  case class Addition(e1: Expr, e2: Expr) extends Expr
  case class Variable(i: Int) extends Expr

  def transform(e: Expr, f: Expr => Option[Expr]): Expr = {
    f(e) match {
      case Some(newExpr) => newExpr
      case None() => e match {
        case Invocation(c, args) =>
          val newC = transform(c, f)
          val newArgs = args.map((x: Expr) => transform(x, f))
          Invocation(newC, newArgs)
        case Addition(e1, e2) =>
          Addition(transform(e1, f), transform(e2, f))
        case Variable(i) => e
      }
    }
  }
}

