/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package xlang

import scala.language.existentials

trait PartialFunctions
  extends oo.SimplePhase
     with SimplyCachedFunctions
     with SimplyCachedSorts
     with oo.SimplyCachedClasses { self =>

  val t: self.s.type
  import s._

  override protected def getContext(symbols: Symbols) = new TransformerContext(symbols)

  protected class TransformerContext(symbols: s.Symbols) extends oo.TreeTransformer {
    override final val s: self.s.type = self.s
    override final val t: self.t.type = self.t

    val optPFClass = symbols.lookup.get[ClassDef]("stainless.lang.~>")

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
        case Seq(MatchCase(_: WildcardPattern, None, _)) => None

        case cases => Some(MatchExpr(scrut, cases :+ MatchCase(
          WildcardPattern(None).copiedFrom(body), None,
          BooleanLiteral(false).copiedFrom(body)
        ).copiedFrom(body)).copiedFrom(body))
      }
    }

    override def transform(e: Expr): Expr = super.transform(e) match {
      case fi @ FunctionInvocation(ast.SymbolIdentifier("stainless.lang.PartialFunction.apply"), _, _) =>
        val FunctionInvocation(_, froms :+ to, Seq(fun)) = fi
        val ct = ClassType(optPFClass.get.id, Seq(tupleTypeWrap(froms), to))

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
  }
}

object PartialFunctions {
  def apply(trees: xlang.Trees)(implicit ctx: inox.Context): ExtractionPipeline {
    val s: trees.type
    val t: trees.type
  } = new PartialFunctions {
    override val s: trees.type = trees
    override val t: trees.type = trees
    override val context = ctx
  }
}
