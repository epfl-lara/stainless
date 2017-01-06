/* Copyright 2009-2016 EPFL, Lausanne */

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

    object transformer extends ast.TreeTransformer {
      val s: self.s.type = self.s
      val t: self.t.type = self.t
    }

    t.NoSymbols
      .withADTs(symbols.adts.values.map(transformer.transform).toSeq)
      .withFunctions(symbols.functions.values.toSeq.sorted(functionOrdering).map { fd =>
        if ((fd.flags contains Inline) && transitivelyCalls(fd, fd)) {
          throw MissformedStainlessCode(fd, "Can't inline recursive function")
        }

        transformer.transform(fd.copy(
          fullBody = exprOps.postMap({
            case fi @ FunctionInvocation(_, _, args) =>
              val tfd = fi.tfd
              if (tfd.fd.flags contains Inline) {
                Some(exprOps.postMap {
                  case Require(pred, body) =>
                    Some(Assert(pred, Some("Inlined precondition"), body))
                  case Ensuring(body, lambda) =>
                    val v = Variable.fresh("res", body.getType)
                    Some(Let(v.toVal, body,
                      Assert(application(lambda, Seq(v)), Some("Inlined postcondition"), v)))
                  case _ => None
                } (exprOps.freshenLocals((tfd.params zip args).foldRight(tfd.fullBody) {
                    case ((vd, e), body) => let(vd, e, body)
                })))
              } else {
                None
              }
            case _ => None
          }, applyRec = true) (fd.fullBody),
          flags = fd.flags - Inline
        ))
      })
  }
}
