/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package inlining

import scala.collection.mutable.{Map => MutableMap}

trait FunctionInlining extends PipelinePhase { self =>
  val s: Trees
  val t: ast.Trees

  private[this] val functionCache: MutableMap[Identifier, Option[t.FunDef]] = MutableMap.empty
  private[this] val sortCache: MutableMap[Identifier, t.ADTSort] = MutableMap.empty

  private object identity extends ast.TreeTransformer {
    val s: self.s.type = self.s
    val t: self.t.type = self.t
  }

  override def nextSymbols(id: Identifier): t.Symbols = {
    val symbols = lastSymbols(id)

    import s._
    import symbols._

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

        def willInline = hasInlineFlag || (hasInlineOnceFlag && !inlinedOnce.contains(tfd.id))

        if (!willInline) {
          return fi
        }

        val body = exprOps.withoutSpecs(tfd.fullBody)
        val uncheckedBody = body match {
          case None => NoTree(tfd.returnType)
          case Some(body) => annotated(body, Unchecked)
        }

        val pre = exprOps.preconditionOf(tfd.fullBody)
        def addPreconditionAssertion(e: Expr) = pre match {
          case None => e
          case Some(pre) => Assert(pre, Some("Inlined precondition of " + tfd.id.name), e).copiedFrom(fi)
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

    for (fd <- symbols.functions.values) {
      val hasInlineFlag = fd.flags contains Inline
      val hasInlineOnceFlag = fd.flags contains InlineOnce

      if (hasInlineFlag && hasInlineOnceFlag) {
        throw MissformedStainlessCode(fd, "Can't annotate a function with both @inline and @inlineOnce")
      }

      if (hasInlineFlag && transitivelyCalls(fd, fd)) {
        throw MissformedStainlessCode(fd, "Can't inline recursive function, use @inlineOnce instead")
      }

      if (hasInlineFlag && exprOps.withoutSpecs(fd.fullBody).isEmpty) {
        throw MissformedStainlessCode(fd, "Inlining function with empty body: not supported, use @inlineOnce instead")
      }
    }

    val newSymbols = t.NoSymbols
      .withSorts(symbols.sorts.values.toSeq.map { sort =>
        sortCache.getOrElseUpdate(sort.id, identity.transform(sort))
      })
      .withFunctions(symbols.functions.values.toSeq.flatMap { fd =>
        functionCache.getOrElseUpdate(fd.id, {
          if ((fd.flags contains Synthetic) && (fd.flags contains Inline)) None
          else Some(identity.transform(fd.copy(
            fullBody = new Inliner(fd).transform(fd.fullBody),
            flags = fd.flags filterNot (f => f == Inline || f == InlineOnce || f == Synthetic)
          )))
        })
      })

    val inlinedOnceFuns = symbols.functions.values.filter(_.flags contains InlineOnce).map(_.id).toSet

    def isCandidate(id: Identifier): Boolean =
      (inlinedOnceFuns contains id) && (symbols.getFunction(id).flags contains Synthetic)

    def isPrunable(id: Identifier): Boolean =
      isCandidate(id) && newSymbols.transitiveCallers(id).forall(isCandidate)

    t.NoSymbols
      .withSorts(newSymbols.sorts.values.toSeq)
      .withFunctions(newSymbols.functions.values.filterNot(fd => isPrunable(fd.id)).toSeq)
  }
}
