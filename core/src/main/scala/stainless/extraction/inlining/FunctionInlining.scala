/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package extraction
package inlining

object optInlinePosts extends inox.FlagOptionDef("inlineposts", false)

trait FunctionInlining extends inox.ast.SymbolTransformer { self =>
  val s: Trees
  val t: extraction.Trees

  def transform(symbols: s.Symbols): t.Symbols = {
    import s._
    import symbols._
    import CallGraphOrderings._

    object transformer extends ast.TreeTransformer {
      val s: self.s.type = self.s
      val t: self.t.type = self.t
    }

    def inlineFunctionInvocations(e: Expr) = {
      exprOps.preMap({
        case fi@FunctionInvocation(_, _, args) =>
          val tfd = fi.tfd
          if ((tfd.fd.flags contains Inline) && transitivelyCalls(tfd.fd, tfd.fd)) {
            throw MissformedStainlessCode(tfd.fd, "Can't inline recursive function: " + tfd.fd.id.name)
          }
          if (tfd.fd.flags contains Inline) {
            val (pre, body, post) = exprOps.breakDownSpecs(tfd.fullBody)
            val uncheckedBody = body match {
              case None => throw MissformedStainlessCode(tfd.fd, "Inlining function with empty body: not supported")
              case Some(body) => Dontcheck(body).copiedFrom(body)
            }
            def addPreconditionAssertion(e: Expr) = pre match {
              case None => e
              case Some(pre) => Assert(pre, Some("Inlined precondition of " + tfd.fd.id.name), e).copiedFrom(fi)
            }
            def addPostconditionAssumption(e: Expr) = post match {
              case None => e
              case Some(lambda) =>
                val v = Variable.fresh("res", e.getType).copiedFrom(e)
                Let(v.toVal, e, Assume(application(lambda, Seq(v)), v).copiedFrom(lambda)).copiedFrom(e)
            }
            val newBody = addPreconditionAssertion(addPostconditionAssumption(uncheckedBody))
            Some(exprOps.freshenLocals((tfd.params zip args).foldRight(newBody: Expr) {
              case ((vd, e), body) => let(vd, e, body)
            }))
          } else {
            None
          }
        case _ => None
      }, applyRec = true)(e)
    }

    t.NoSymbols
      .withADTs(symbols.adts.values.map(transformer.transform).toSeq)
      .withFunctions(symbols.functions.values.toSeq.sorted(functionOrdering).flatMap { fd =>
        if ((fd.flags contains Inline) && transitivelyCalls(fd, fd)) {
          throw MissformedStainlessCode(fd, "Can't inline recursive function")
        }

        if ((fd.flags contains Implicit) && (fd.flags contains Inline)) {
          None
        } else {
          Some(transformer.transform(fd.copy(
            fullBody = inlineFunctionInvocations(fd.fullBody),
            flags = fd.flags - Inline
          )))
        }
      })
  }
}
