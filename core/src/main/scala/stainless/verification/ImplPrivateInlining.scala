/* Copyright 2009-2020 EPFL, Lausanne */

package stainless
package verification

/**
 * Inline functions marked ImplPrivate.
 **/
trait ImplPrivateInlining extends transformers.TreeTransformer {
  val s: ast.Trees
  val t: s.type

  val context: inox.Context

  implicit val symbols: s.Symbols

  import symbols._
  import t._

  override def transform(expr: s.Expr): t.Expr = expr match {
    case fi: FunctionInvocation if fi.tfd.flags.contains(ImplPrivate) =>
      inlineFunctionInvocations(fi.copy(args = fi.args map transform).copiedFrom(fi)).copiedFrom(fi)

    case _ => super.transform(expr)
  }

  private def inlineFunctionInvocations(fi: FunctionInvocation): Expr = {
    val (tfd, args) = (fi.tfd, fi.args)

    import exprOps._
    val specced = BodyWithSpecs(tfd.fullBody)

    if (specced.getSpec(PreconditionKind).isDefined) {
      context.reporter.internalError(s"Unexpected precondition on @implPrivate function ${fi.tfd.id}")
      return fi
    }
    if (specced.getSpec(PostconditionKind).isDefined) {
      context.reporter.internalError(s"Unexpected postcondition on @implPrivate function ${fi.tfd.id}")
      return fi
    }

    val result = (tfd.params zip args).foldRight(specced.body) {
      case ((vd, e), body) => let(vd, e, body).setPos(fi)
    }

    val freshened = exprOps.freshenLocals(result)

    // NOTE: We assume that there is nothing further to IP-inline in ImplPrivate bodies
    freshened
  }
}

object ImplPrivateInlining {
  def apply(p: Program, ctx: inox.Context): inox.transformers.SymbolTransformer {
    val s: p.trees.type
    val t: p.trees.type
  } = new inox.transformers.SymbolTransformer {
    val s: p.trees.type = p.trees
    val t: p.trees.type = p.trees

    def transform(syms: s.Symbols): t.Symbols = {
      object inlining extends ImplPrivateInlining {
        val s: p.trees.type = p.trees
        val t: p.trees.type = p.trees
        val symbols: p.symbols.type = p.symbols
        val context: inox.Context = ctx
      }

      t.NoSymbols
        .withFunctions(syms.functions.values.toSeq.collect {
          case fd if fd.flags.contains(t.ImplPrivate) =>
            // We assume there is nothing to IP-inline in ImplPrivate functions
            fd

          case fd =>
            val specced = s.exprOps.BodyWithSpecs(fd.fullBody)
            val newSpecced = specced.copy(
              specs = specced.specs.map(_.transform(inlining.transform(_))),
              body = inlining.transform(specced.body)
            )

            new t.FunDef(
              fd.id,
              fd.tparams map inlining.transform,
              fd.params map inlining.transform,
              inlining.transform(fd.returnType),
              newSpecced.reconstructed,
              fd.flags map inlining.transform
            ).copiedFrom(fd)
        })
        .withSorts(syms.sorts.values.toSeq.map(inlining.transform))
    }
  }
}
