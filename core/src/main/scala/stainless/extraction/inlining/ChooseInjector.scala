/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package inlining

class ChooseInjector(override val s: inlining.Trees,
                     override val t: inlining.Trees)
                    (using override val context: inox.Context)
  extends CachingPhase with IdentitySorts { self =>

  import s._
  import exprOps._

  override protected final val funCache = new ExtractionCache[s.FunDef, FunctionResult]((fd, context) =>
    getDependencyKey(fd.id)(using context.symbols)
  )

  override protected type FunctionResult = Seq[t.FunDef]
  override protected def registerFunctions(symbols: t.Symbols, functions: Seq[Seq[t.FunDef]]): t.Symbols =
    symbols.withFunctions(functions.flatten)

  protected lazy val newIdentifier = new utils.ConcurrentCached[Identifier, Identifier](_.freshen)

  override def getContext(symbols: s.Symbols) = new TransformerContext(symbols)
  protected class TransformerContext(val symbols: s.Symbols) extends inox.transformers.TreeTransformer {
    override final val s: self.s.type = self.s
    override final val t: self.t.type = self.t

    val toReplace: Set[Identifier] = symbols.functions.values.filter {
      fd => fd.flags.contains(Extern) || fd.flags.contains(Opaque)
    }.map(_.id).toSet

    override def transform(e: s.Expr): t.Expr = e match {
      case fi @ s.FunctionInvocation(id, tps, args) if toReplace(id) =>
        t.FunctionInvocation(newIdentifier(id), tps.map(transform), args.map(transform))
      case _ => super.transform(e)
    }
  }

  override def extractFunction(context: TransformerContext, fd: s.FunDef): Seq[t.FunDef] = {
    val symbols = context.symbols
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

    if (context.toReplace.contains(fd.id)) {
      val choose = post
        .map { case Postcondition(Lambda(Seq(vd), post)) =>
          Choose(vd, freshenLocals(specced.wrapLets(post)))
        }
        .getOrElse {
          Choose(ValDef(FreshIdentifier("res", true), fd.returnType), BooleanLiteral(true))
        }
        .copiedFrom(fd)
      val newSpecced = specced.copy(body = choose)
      val fdCopy = fd.copy(id = newIdentifier(fd.id), fullBody = newSpecced.reconstructed, flags = fd.flags :+ DropVCs).setPos(fd)
      Seq(context.transform(fdCopy), context.transform(fd))
    } else {
      val newSpecced = specced.copy(body = injectChooses(specced.body))
      val res = fd.copy(fullBody = newSpecced.reconstructed).setPos(fd)
      Seq(context.transform(res))
    }
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
