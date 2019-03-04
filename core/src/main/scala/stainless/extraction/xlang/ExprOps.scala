/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package extraction
package xlang

trait ExprOps extends innerclasses.ExprOps { self =>
  protected val trees: Trees
  import trees._

  /** Extracts the body without its specification
    *
    * [[Expressions.Expr]] trees contain its specifications as part of certain nodes.
    * This function helps extracting only the body part of an expression
    *
    * @return An option type with the resulting expression if not [[Expressions.NoTree]]
    * @see [[Expressions.Ensuring]]
    * @see [[Expressions.Require]]
    */
  override def withoutSpecs(expr: Expr): Option[Expr] = expr match {
    case Let(i, e, b)                    => withoutSpecs(b).map(Let(i, e, _).copiedFrom(expr))
    case Require(pre, b)                 => Option(b).filterNot(_.isInstanceOf[NoTree])
    case Ensuring(Require(pre, b), post) => Option(b).filterNot(_.isInstanceOf[NoTree])
    case Ensuring(b, post)               => Option(b).filterNot(_.isInstanceOf[NoTree])
    case b                               => Option(b).filterNot(_.isInstanceOf[NoTree])
  }

  /** Returns the precondition of an expression wrapped in Option */
  override def preconditionOf(expr: Expr): Option[Expr] = expr match {
    case Let(i, e, b)                 => preconditionOf(b).map(Let(i, e, _).copiedFrom(expr))
    case Require(pre, _)              => Some(pre)
    case Ensuring(Require(pre, _), _) => Some(pre)
    case b                            => None
  }

  /** Returns the postcondition of an expression wrapped in Option */
  override def postconditionOf(expr: Expr): Option[Lambda] = expr match {
    case Let(i, e, b)      => postconditionOf(b).map(l => l.copy(body = Let(i, e, l.body).copiedFrom(expr)).copiedFrom(l))
    case Ensuring(_, post) => Some(post)
    case _                 => None
  }
}
