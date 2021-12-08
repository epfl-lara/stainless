/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification

class ChooseInjector private(val trees: ast.Trees)
                            (override val s: trees.type,
                             override val t: trees.type)
  extends inox.transformers.SymbolTransformer {

  def this(trees: ast.Trees) = this(trees)(trees, trees)

  import trees._
  import exprOps._

  override def transform(symbols: Symbols): Symbols = {
    t.NoSymbols
      .withSorts(symbols.sorts.values.toSeq)
      .withFunctions(symbols.functions.values.toSeq.map { fd =>

        val specced = BodyWithSpecs(fd.fullBody)
        val post = specced.getSpec(PostconditionKind)

        def injectChooses(e: Expr): Expr = e match {
          case NoTree(tpe) =>
            val vd = ValDef(FreshIdentifier("res"), tpe, Seq(DropVCs)).copiedFrom(e)
            // FIXME: Use `specced.wrapLets` as below, so `choose` refers to function parameters?
            val pred = post
              .map(post => symbols.application(post.expr, Seq(vd.toVariable)))
              .getOrElse(BooleanLiteral(true))
              .copiedFrom(tpe)
            Choose(vd, pred).copiedFrom(e)

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

        val newSpecced = if ((fd.flags contains Extern) || (fd.flags contains Opaque)) {
          val choose = post
            .map { case Postcondition(Lambda(Seq(vd), post)) =>
              Choose(vd, freshenLocals(specced.wrapLets(post)))
            }
            .getOrElse {
              Choose(ValDef(FreshIdentifier("res", true), fd.returnType), BooleanLiteral(true))
            }
            .copiedFrom(fd)
          val remainingSpecs = specced.specs.filter {
            case _: Precondition | _: LetInSpec => true
            case _ => false
          }
          specced.copy(specs = remainingSpecs, body = choose)
        } else {
          specced.copy(body = injectChooses(specced.body))
        }

        fd.copy(fullBody = newSpecced.reconstructed)
    })
  }
}

object ChooseInjector {
  def apply(p: Program): inox.transformers.SymbolTransformer {
    val s: p.trees.type
    val t: p.trees.type
  } = {
    class Impl(override val trees: p.trees.type) extends ChooseInjector(trees)
    new Impl(p.trees)
  }
}
