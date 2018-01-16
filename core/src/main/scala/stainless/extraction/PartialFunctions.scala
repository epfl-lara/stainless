/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package extraction

import scala.language.existentials

object PartialFunctions extends inox.ast.SymbolTransformer {
  val s: xlang.trees.type = xlang.trees
  val t: xlang.trees.type = xlang.trees
  import xlang.trees._

  override def transform(symbols: Symbols): Symbols = symbols.transform(new oo.TreeTransformer {
    val s: xlang.trees.type = xlang.trees
    val t: xlang.trees.type = xlang.trees

    val optPFApply = symbols.lookup.get[FunDef]("stainless.lang.PartialFunction.apply")
    val optPFClass = symbols.lookup.get[ClassDef]("stainless.lang.$tilde$greater")

    override def transform(e: Expr): Expr = super.transform(e) match {
      case fi: FunctionInvocation =>
        optPFApply
          .filter(_.id == fi.id)
          .map { fd =>
            val FunctionInvocation(_, Seq(from, to), Seq(fun)) = fi
            val ct = ClassType(optPFClass.get.id, Seq(from, to))

            val (pre, body) = fun match {
              case Lambda(Seq(vd), body0) =>
                val preOpt = exprOps.preconditionOf(body0)
                val bareBody = exprOps.withPrecondition(body0, None)
                val modifiedBody = preOpt match {
                  case None => bareBody
                  case Some(pre) => Assume(pre, bareBody)
                }

                val pre = Lambda(Seq(vd), preOpt getOrElse BooleanLiteral(true))
                val body = Lambda(Seq(vd), modifiedBody)

                (pre, body)

              case x =>
                throw new frontend.UnsupportedCodeException(
                  fun.getPos,
                  s"Unexpected $x [${x.getClass}] instead of a lambda when " +
                  "unapply syntactic sugar for partial function creation.")
            }

            ClassConstructor(ct, Seq(pre, body))
          }.getOrElse(fi)

      case other => other
    }
  })
}
