/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package throwing

trait Trees extends oo.Trees {

  protected def getExceptionType(implicit s: Symbols): Option[Type] =
    s.lookup.get[ADTSort]("stainless.lang.Exception").map(sort => ADTType(sort.id, Seq()))

  /** Throwing clause of an [[ast.Expressions.Expr]]. Corresponds to the Stainless keyword *throwing*
    *
    * @param body The body of the expression. It can contain at most one [[ast.Expressions.Require]] and
    *             one [[ast.Expressions.Ensuring]] sub-expression.
    * @param pred The predicate on exceptions to satisfy. It should be a function whose argument type
    *             is `stainless.lang.Exception` and defines the exceptional cases of this function.
    */
  sealed case class Throwing(body: Expr, pred: Lambda) extends Expr with CachingTyped {
    override protected def computeType(implicit s: Symbols): Type = (pred.getType, getExceptionType) match {
      case (FunctionType(Seq(expType), BooleanType()), Some(tpe)) => checkParamType(tpe, expType, body.getType)
      case _ => Untyped
    }
  }

  /** Throw expression. Corresponds to the Scala keyword *throw*
    *
    * @param ex The exception to be thrown.
    */
  sealed case class Throw(ex: Expr) extends Expr with CachingTyped {
    override protected def computeType(implicit s: Symbols): Type = getExceptionType match {
      case Some(tpe) => checkParamType(ex.getType, tpe, NothingType())
      case _ => Untyped
    }
  }
}
