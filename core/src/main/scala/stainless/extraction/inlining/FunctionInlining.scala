/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package inlining

trait FunctionInlining extends CachingPhase with IdentitySorts { self =>
  val s: Trees
  val t: trace.Trees
  import s._

  // The function inlining transformation depends on all (transitive) callees
  // that will require inlining.
  override protected final val funCache = new ExtractionCache[s.FunDef, FunctionResult]({(fd, symbols) =>
    FunctionKey(fd) + SetKey(
      symbols.dependencies(fd.id)
        .flatMap(id => symbols.lookupFunction(id))
        .filter(_.flags exists { case Inline | InlineOnce => true case _ => false })
    )
  })

  override protected type FunctionResult = Option[t.FunDef]
  override protected type TransformerContext = s.Symbols
  override protected def getContext(symbols: s.Symbols) = symbols

  private[this] object identity extends transformers.TreeTransformer {
    override val s: self.s.type = self.s
    override val t: self.t.type = self.t
  }

  override protected def registerFunctions(symbols: t.Symbols, functions: Seq[Option[t.FunDef]]): t.Symbols =
    symbols.withFunctions(functions.flatten)

  override protected def extractFunction(symbols: s.Symbols, fd: s.FunDef): Option[t.FunDef] = {
    import symbols._

    class Inliner(inlinedOnce: Set[Identifier] = Set()) extends s.SelfTreeTransformer {

      override def transform(expr: s.Expr): t.Expr = expr match {
        case fi: FunctionInvocation =>
          inlineFunctionInvocations(fi.copy(args = fi.args map transform).copiedFrom(fi)).copiedFrom(fi)

        case _ => super.transform(expr)
      }

      private def inlineFunctionInvocations(fi: FunctionInvocation): Expr = {
        import exprOps._
        val (tfd, args) = (fi.tfd, fi.args)

        val isOpaque = tfd.fd.flags contains Opaque
        val isSynthetic = tfd.fd.flags contains Synthetic
        val hasInlineFlag = tfd.fd.flags contains Inline
        val hasInlineOnceFlag = tfd.fd.flags contains InlineOnce

        def willInline = hasInlineFlag || (hasInlineOnceFlag && !inlinedOnce.contains(tfd.id))

        if (!willInline) return fi

        val specced = BodyWithSpecs(tfd.fullBody)

        // We need to keep the body as-is for `@synthetic` methods, such as
        // `copy` or implicit conversions for implicit classes, in order to
        // later on check that the class invariant is valid.
        val body = specced.bodyOpt match {
          case Some(body) if isSynthetic => body
          case Some(body) if !isOpaque => annotated(body, Unchecked).setPos(fi)
          case _ => NoTree(tfd.returnType).copiedFrom(tfd.fullBody)
        }

        val pre = specced.specs.filter(spec => spec.kind == LetKind || spec.kind == PreconditionKind)
        val maxPre = pre.count(_.kind == PreconditionKind)
        def addPreconditionAssertions(e: Expr): Expr = {
          pre.foldRight((e, maxPre)) {
            case (spec @ LetInSpec(vd, e0), (acc, i)) => (Let(vd, annotated(e0, Unchecked), acc).setPos(fi), i)
            case (spec @ Precondition(cond), (acc, i)) =>
              val num = if (i == 1) "" else s" ($i)"
              // the assertion is not itself marked `Unchecked` (as it needs to be checked)
              // but `cond` should not generate additional VCs and is marked with `Unchecked`
              val condVal = ValDef.fresh("cond", BooleanType()).setPos(fi)
              (
                Let(condVal, annotated(cond, Unchecked),
                  Assert(condVal.toVariable.setPos(fi), Some(s"Inlined precondition$num of " + tfd.id.asString), acc
                ).copiedFrom(fi)).copiedFrom(fi),
                i-1
              )
          }._1
        }

        val post = specced.getSpec(PostconditionKind)
        def addPostconditionAssumption(e: Expr): Expr = post.map(_.expr) match {
          // We can't assume the post on @synthetic methods as it won't be checked anywhere.
          // It is thus inlined into an assertion here.
          case Some(Lambda(Seq(vd), post)) if isSynthetic =>
            val err = Some("Inlined postcondition of " + tfd.id.name)
            val postVal = ValDef.fresh("post", BooleanType()).setPos(fi)
            Let(vd, e,
              Let(postVal, annotated(post, Unchecked),
                Assert(postVal.toVariable.setPos(fi), err, vd.toVariable.copiedFrom(fi)
            ).copiedFrom(fi)).copiedFrom(fi)).copiedFrom(fi)
          case Some(Lambda(Seq(vd), post)) =>
            Let(vd, e, Assume(annotated(post, Unchecked), vd.toVariable.copiedFrom(fi)).copiedFrom(fi)).copiedFrom(fi)
          case _ => e
        }


        val res = ValDef.fresh("inlined", tfd.returnType)
        val inlined = addPreconditionAssertions(addPostconditionAssumption(body))

        // We bind the inlined expression in a let to avoid propagating
        // the @unchecked annotation to postconditions, etc.
        val newBody = let(res, inlined, res.toVariable.setPos(fi)).setPos(fi)

        val result = (tfd.params zip args).foldRight(newBody) {
          case ((vd, e), body) => let(vd, e, body).setPos(fi)
        }

        val freshened = exprOps.freshenLocals(result)

        val inliner = new Inliner(if (hasInlineOnceFlag) inlinedOnce + tfd.id else inlinedOnce)
        inliner.transform(freshened)
      }
    }

    if ((fd.flags contains Synthetic) && (fd.flags contains Inline)) None
    else Some(identity.transform(fd.copy(
      fullBody = new Inliner().transform(fd.fullBody),
      flags = fd.flags filterNot (f => f == Inline || f == InlineOnce)
    )))
  }

  override protected def extractSymbols(context: TransformerContext, symbols: s.Symbols): t.Symbols = {
    for (fd <- symbols.functions.values) {
      val hasInlineFlag = fd.flags contains Inline
      val hasInlineOnceFlag = fd.flags contains InlineOnce

      if (hasInlineFlag && hasInlineOnceFlag) {
        throw MalformedStainlessCode(fd, "Can't annotate a function with both @inline and @inlineOnce")
      }

      if (hasInlineFlag && context.transitivelyCalls(fd, fd)) {
        throw MalformedStainlessCode(fd, "Can't inline recursive function, use @inlineOnce instead")
      }

      if (hasInlineFlag && exprOps.BodyWithSpecs(fd.fullBody).bodyOpt.isEmpty) {
        throw MalformedStainlessCode(fd, "Inlining function with empty body: not supported, use @inlineOnce instead")
      }
    }

    val newSymbols = super.extractSymbols(context, symbols)

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

object FunctionInlining {
  def apply(ts: Trees, tt: trace.Trees)(implicit ctx: inox.Context): ExtractionPipeline {
    val s: ts.type
    val t: tt.type
  } = new FunctionInlining {
    override val s: ts.type = ts
    override val t: tt.type = tt
    override val context = ctx
  }
}
