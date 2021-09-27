/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package inlining

trait ChooseInjector extends CachingPhase with SimplyCachedFunctions with SimpleFunctions with IdentitySorts { self =>

  implicit val context: inox.Context

  val s: inlining.Trees
  val t: s.type

  import s._
  import exprOps._

  type TransformerContext = Symbols
  def getContext(symbols: Symbols) = symbols

  override def extractFunction(symbols: TransformerContext, fd: s.FunDef): t.FunDef = {
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
      specced.copy(body = choose)
    } else {
      specced.copy(body = injectChooses(specced.body))
    }

    fd.copy(fullBody = newSpecced.reconstructed).setPos(fd)
  }
}

object ChooseInjector {
  def apply(it: inlining.Trees)(implicit ctx: inox.Context): ExtractionPipeline {
    val s: it.type
    val t: it.type
  } = new {
    override val context = ctx
    override val s: it.type = it
    override val t: it.type = it
  } with ChooseInjector
}
