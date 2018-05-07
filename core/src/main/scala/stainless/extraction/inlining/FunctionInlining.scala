/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package inlining

trait FunctionInlining extends inox.ast.SymbolTransformer { self =>
  val s: Trees
  val t: extraction.Trees

  def transform(symbols: s.Symbols): t.Symbols = {
    import s._
    import symbols._
    import CallGraphOrderings._

    class Inliner(within: FunDef, inlinedOnce: Set[Identifier] = Set()) extends s.SelfTreeTransformer {

      override def transform(expr: s.Expr): t.Expr = expr match {
        case fi: FunctionInvocation if fi.tfd.id != within.id =>
          inlineFunctionInvocations(fi.copy(args = fi.args map transform))

        case _ => super.transform(expr)
      }

      private def inlineFunctionInvocations(fi: FunctionInvocation): Expr = {
        val (tfd, args) = (fi.tfd, fi.args)

        val hasInlineFlag = tfd.fd.flags contains Inline
        val hasInlineOnceFlag = tfd.fd.flags contains InlineOnce

        if (hasInlineFlag && transitivelyCalls(tfd.fd, tfd.fd)) {
          throw MissformedStainlessCode(tfd.fd, "Can't inline recursive function, use @inlineOnce instead")
        }

        def willInline = hasInlineFlag || (hasInlineOnceFlag && !inlinedOnce.contains(tfd.id))
        if (!willInline) {
          return fi
        }

        val body = exprOps.withoutSpecs(tfd.fullBody)
        val uncheckedBody = body match {
          case Some(body) => annotated(body, Unchecked)
          case None if hasInlineOnceFlag => NoTree(tfd.returnType)
          case None => throw MissformedStainlessCode(tfd.fd, "Inlining function with empty body: not supported, use @inlineOnce instead")
        }

        val pre = exprOps.preconditionOf(tfd.fullBody)
        def addPreconditionAssertion(e: Expr) = pre match {
          case None => e
          case Some(pre) => Assert(pre, Some("Inlined precondition of " + tfd.fd.id.name), e).copiedFrom(fi)
        }

        val post = exprOps.postconditionOf(tfd.fullBody)
        def addPostconditionAssumption(e: Expr) = post match {
          case None => e
          case Some(Lambda(Seq(vd), post)) =>
            Let(vd, e, Assume(post, vd.toVariable).copiedFrom(fi)).copiedFrom(fi)
        }

        val newBody = addPreconditionAssertion(addPostconditionAssumption(uncheckedBody))
        val result = exprOps.freshenLocals {
          (tfd.params zip args).foldRight(newBody: Expr) {
            case ((vd, e), body) => let(vd, e, body)
          }
        }

        val inliner = new Inliner(within, if (hasInlineOnceFlag) inlinedOnce + tfd.id else inlinedOnce)
        inliner.transform(result)
      }
    }

    object transformer extends ast.TreeTransformer {
      val s: self.s.type = self.s
      val t: self.t.type = self.t
    }

    val afterInlining = s.NoSymbols
      .withSorts(symbols.sorts.values.toSeq)
      .withFunctions(symbols.functions.values.toSeq.sorted(functionOrdering).flatMap { fd =>
        if ((fd.flags contains Inline) && (fd.flags contains InlineOnce)) {
          throw MissformedStainlessCode(fd, "Can't annotate a function with both @inline and @inlineOnce")
        }
        if ((fd.flags contains Inline) && transitivelyCalls(fd, fd)) {
          throw MissformedStainlessCode(fd, "Can't inline recursive function, use @inlineOnce instead")
        }

        if ((fd.flags contains Synthetic) && (fd.flags contains Inline)) {
          None
        } else {
          Some(fd.copy(
            fullBody = new Inliner(fd).transform(fd.fullBody),
            flags = fd.flags filterNot (f => f == Inline || f == InlineOnce)
          ))
        }
      })

    val inlinedOnceFuns = symbols.functions.values.filter(_.flags contains InlineOnce).map(_.id).toSet
    def isCandidate(fd: FunDef) = inlinedOnceFuns.contains(fd.id) && fd.flags.contains(Synthetic)

    val pruned = afterInlining.functions.values.toSeq.flatMap { fd =>
      val callers = afterInlining.transitiveCallers(fd)
      if (isCandidate(fd) && callers.forall(isCandidate)) None
      else Some(fd.copy(flags = fd.flags filterNot (_ == Synthetic)))
    }

    t.NoSymbols
      .withSorts(afterInlining.sorts.values.map(transformer.transform).toSeq)
      .withFunctions(pruned.map(transformer.transform).toSeq)
  }
}
