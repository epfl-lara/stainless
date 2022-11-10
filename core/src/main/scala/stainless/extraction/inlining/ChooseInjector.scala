/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package inlining

class ChooseInjector(override val s: inlining.Trees,
                     override val t: inlining.Trees)
                    (using override val context: inox.Context)
  extends CachingPhase with SimpleFunctions with IdentitySorts { self =>

  import s._
  import exprOps._

  override protected final val funCache = new ExtractionCache[s.FunDef, FunctionResult]((fd, symbols) =>
    getDependencyKey(fd.id)(using symbols)
  )

  override protected type TransformerContext = s.Symbols
  override def getContext(symbols: s.Symbols): TransformerContext = symbols

  private[this] class Identity(override val s: self.s.type, override val t: self.t.type) extends transformers.ConcreteTreeTransformer(s, t)
  private[this] val identity = new Identity(self.s, self.t)

  override def extractFunction(symbols: TransformerContext, fd: s.FunDef): t.FunDef = {
    val specced = BodyWithSpecs(fd.fullBody)
    val post = specced.getSpec(PostconditionKind)

    def injectChooses(e: s.Expr): s.Expr = e match {
      case s.NoTree(tpe) =>
        val vd = ValDef(FreshIdentifier("res"), tpe, Seq(DropVCs)).copiedFrom(e)
        // FIXME: Use `specced.wrapLets` as below, so `choose` refers to function parameters?
        val pred = post
          .map(post => symbols.application(post.expr, Seq(vd.toVariable)))
          .getOrElse(s.BooleanLiteral(true))
          .copiedFrom(tpe)
        s.Choose(vd, pred).copiedFrom(e)

      case ie @ s.IfExpr(c, t, e) =>
        s.IfExpr(c, injectChooses(t), injectChooses(e)).copiedFrom(ie)

      case me @ s.MatchExpr(scrut, cases) =>
        s.MatchExpr(scrut, cases.map {
          cse => cse.copy(rhs = injectChooses(cse.rhs)).copiedFrom(cse)
        }).copiedFrom(me)

      case let @ s.Let(x, v, b) =>
        s.Let(x, v, injectChooses(b)).copiedFrom(let)

      case _ => e
    }

    val newSpecced = specced.copy(body = injectChooses(specced.body))
    identity.transform(fd.copy(fullBody = newSpecced.reconstructed).setPos(fd))
  }
}

object ChooseInjector {
  def apply(it: inlining.Trees)(using inox.Context): ExtractionPipeline {
    val s: it.type
    val t: it.type
  } = {
    class Impl(override val s: it.type, override val t: it.type) extends ChooseInjector(s, t)
    new Impl(it, it)
  }
}
