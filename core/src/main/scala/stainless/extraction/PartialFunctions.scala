/* Copyright 2009-2018 EPFL, Lausanne */

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

    val optPFClass = symbols.lookup.get[ClassDef]("stainless.lang.$tilde$greater")

    override def transform(e: Expr): Expr = super.transform(e) match {
      case fi @ FunctionInvocation(ast.SymbolIdentifier("stainless.lang.PartialFunction.apply"), _, _) =>
        val FunctionInvocation(_, froms :+ to, Seq(fun)) = fi
        val ct = ClassType(optPFClass.get.id, Seq(tupleTypeWrap(froms), to), Seq())

        val (pre, body) = fun match {
          case Lambda(vds, body0) =>
            val (preOpt, bareBody) = body0 match {
              // Call to another function: Lift the function's definition
              case fi2: FunctionInvocation =>
                (exprOps.preconditionOf(fi2.inlined(symbols)), fi2)

              // scala.PartialFunction: Infer pattern match condition
              case m: MatchExpr =>
                (inferPrecondition(m), m)

              case _ =>
                (exprOps.preconditionOf(body0), exprOps.withPrecondition(body0, None))
            }

            val modifiedBody = preOpt match {
              case None => bareBody
              case Some(pre) => Assume(pre, bareBody).setPos(bareBody)
            }

            val (vd, funArgs) = vds match {
              case Seq(vd) => (vd, Seq(vd.toVariable))
              case _ =>
                val vd = ValDef(FreshIdentifier("p"), tupleTypeWrap(vds.map(_.tpe)))
                val funArgs = vds.indices.map(i => TupleSelect(vd.toVariable, i + 1))
                (vd, funArgs)
            }

            val subst = (vds zip funArgs).toMap
            val pre = Lambda(Seq(vd), exprOps.replaceFromSymbols(subst, preOpt getOrElse BooleanLiteral(true))).setPos(fi)
            val body = Lambda(Seq(vd), exprOps.replaceFromSymbols(subst, modifiedBody)).setPos(modifiedBody)
            (pre, body)

          case x =>
            throw new frontend.UnsupportedCodeException(
              fun.getPos,
              s"Unexpected $x [${x.getClass}] instead of a lambda when " +
              "unapply syntactic sugar for partial function creation.")
        }

        ClassConstructor(ct, Seq(pre, body)).setPos(fi)

      case other => other
    }

    /** Infer the partial function's precondition, by replacing every
     *  right-hand side of the pattern match with `true`.
     *  If there is only a single case, and it is a wildcard,
     *  we don't need to infer any precondition.
     */
    def inferPrecondition(body: MatchExpr): Option[Expr] = {
      val MatchExpr(scrut, cases) = body
      val rewrittenCases = cases map { c =>
        c.copy(rhs = BooleanLiteral(true).copiedFrom(c))
      }

      rewrittenCases match {
        case Seq(MatchCase(_: WildcardPattern, None, _)) =>
          None

        case cases =>
          val fallback = MatchCase(WildcardPattern(None), None, BooleanLiteral(false)).copiedFrom(body)
          Some(MatchExpr(scrut, cases :+ fallback).copiedFrom(body))
      }
    }

  })
}
