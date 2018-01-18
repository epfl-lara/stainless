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

    val optPFClass = symbols.lookup.get[ClassDef]("stainless.lang.$tilde$greater")

    override def transform(e: Expr): Expr = super.transform(e) match {
      case fi @ FunctionInvocation(ast.SymbolIdentifier("stainless.lang.PartialFunction.apply"), _, _) =>
        val FunctionInvocation(_, froms :+ to, Seq(fun)) = fi
        val ct = ClassType(optPFClass.get.id, Seq(tupleTypeWrap(froms), to))

        val (pre, body) = fun match {
          case Lambda(vds, body0) =>
            val (preOpt, bareBody) = body0 match {
              case fi2: FunctionInvocation =>
                (exprOps.preconditionOf(fi2.inlined(symbols)), fi2)
              case _ =>
                (exprOps.preconditionOf(body0), exprOps.withPrecondition(body0, None))
            }

            val modifiedBody = preOpt match {
              case None => bareBody
              case Some(pre) => Assume(pre, bareBody)
            }

            val (vd, funArgs) = vds match {
              case Seq(vd) => (vd, Seq(vd.toVariable))
              case _ =>
                val vd = ValDef(FreshIdentifier("p"), tupleTypeWrap(vds.map(_.tpe)))
                val funArgs = vds.indices.map(i => TupleSelect(vd.toVariable, i + 1))
                (vd, funArgs)
            }

            val subst = (vds zip funArgs).toMap
            val pre = Lambda(Seq(vd), exprOps.replaceFromSymbols(subst, preOpt getOrElse BooleanLiteral(true)))
            val body = Lambda(Seq(vd), exprOps.replaceFromSymbols(subst, modifiedBody))
            (pre, body)

          case x =>
            throw new frontend.UnsupportedCodeException(
              fun.getPos,
              s"Unexpected $x [${x.getClass}] instead of a lambda when " +
              "unapply syntactic sugar for partial function creation.")
        }

        ClassConstructor(ct, Seq(pre, body))

      case other => other
    }
  })
}
