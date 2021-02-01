/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification

trait ChooseInjector extends inox.transformers.SymbolTransformer {
  val trees: ast.Trees
  val s: trees.type = trees
  val t: trees.type = trees
  import trees._
  import exprOps._

  override def transform(symbols: Symbols): Symbols = {
    t.NoSymbols
      .withSorts(symbols.sorts.values.toSeq)
      .withFunctions(symbols.functions.values.toSeq.map { fd =>

        val specced = BodyWithSpecs(fd.fullBody)
        val post = specced.getSpec(PostconditionKind).map(s => s.expr)

        def injectChooses(e: Expr): Expr = e match {
          case NoTree(tpe) =>
            val vd = ValDef(FreshIdentifier("res"), tpe, Seq(Unchecked)).copiedFrom(e)
            Choose(vd, post
              .map(l => symbols.application(l, Seq(vd.toVariable)))
              .getOrElse(BooleanLiteral(true))
              .copiedFrom(tpe)
            ).copiedFrom(e)

          case ie @ IfExpr(c, t, e) =>
            IfExpr(c, injectChooses(t), injectChooses(e)).copiedFrom(ie)

          case me @ MatchExpr(scrut, cases) =>
            MatchExpr(scrut, cases.map {
              cse => cse.copy(rhs = injectChooses(cse.rhs)).copiedFrom(cse)
            }).copiedFrom(me)

          case let @ Let(x, v, b) =>
            Let(x, v, injectChooses(b)).copiedFrom(let)

          case _ => e
        }

        val newBody = if ((fd.flags contains Extern) || (fd.flags contains Opaque)) {
          val Lambda(Seq(vd), post) = specced.getSpec(PostconditionKind).map(post => post.expr).getOrElse {
            Lambda(Seq(ValDef.fresh("res", fd.returnType)), BooleanLiteral(true))
          }

          specced.getSpec(PreconditionKind).map(s => s.expr) match {
            case Some(pre) => Require(pre, Choose(vd, post))
            case None => Choose(vd, post)
          }
        } else {
          val newBody = injectChooses(specced.bodyOpt.getOrElse(NoTree(fd.returnType)))
          specced.withBody(newBody).reconstructed
        }

        fd.copy(fullBody = newBody)
    })
  }
}

object ChooseInjector {
  def apply(p: Program): inox.transformers.SymbolTransformer {
    val s: p.trees.type
    val t: p.trees.type
  } = new {
    val trees: p.trees.type = p.trees
  } with ChooseInjector
}
