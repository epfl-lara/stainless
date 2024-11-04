/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package inlining

class FunctionInlining(override val s: Trees, override val t: trace.Trees)
                      (using override val context: inox.Context)
  extends CachingPhase
     with NoSummaryPhase
     with IdentitySorts { self =>
  import s._

  // The function inlining transformation depends on all (transitive) callees
  // that will require inlining.
  override protected final val funCache = new ExtractionCache[s.FunDef, (FunctionResult, FunctionSummary)]({(fd, symbols) =>
    FunctionKey(fd) + SetKey(
      symbols.dependencies(fd.id)
        .flatMap(id => symbols.lookupFunction(id))
        .filter(_.flags exists { case Inline | InlineOnce => true case _ => false })
    )
  })

  override protected type FunctionResult = Option[t.FunDef]
  override protected type TransformerContext = s.Symbols
  override protected def getContext(symbols: s.Symbols) = symbols

  private class FnInliningIdentityImpl(override val s: self.s.type, override val t: self.t.type)
    extends transformers.ConcreteTreeTransformer(s, t)

  private val identity = new FnInliningIdentityImpl(self.s, self.t)

  override protected def registerFunctions(symbols: t.Symbols, functions: Seq[Option[t.FunDef]]): t.Symbols =
    symbols.withFunctions(functions.flatten)

  override protected def extractFunction(symbols: s.Symbols, fd: s.FunDef): (Option[t.FunDef], Unit) = {
    import symbols.{given, _}

    class Inliner(inlinedOnce: Set[Identifier] = Set()) extends s.ConcreteStainlessSelfTreeTransformer {

      override def transform(expr: Expr): Expr = expr match {
        case fi: FunctionInvocation =>
          inlineFunctionInvocations(fi.copy(args = fi.args map transform).copiedFrom(fi)).copiedFrom(fi)

        case _ => super.transform(expr)
      }

      // values that can be inlined directly, without being let-bound
      private def isValue(e: Expr): Boolean = e match {
        case _: Variable => true
        case UnitLiteral() => true
        case BooleanLiteral(_) => true
        case IntegerLiteral(_) => true
        case BVLiteral(_, _, _) => true
        case Tuple(es) => es.forall(isValue)
        case FiniteArray(args, base) => args.forall(isValue)
        case LargeArray(elems, default, _, _) => elems.map(_._2).forall(isValue) && isValue(default)
        case ADT(_, _, args) => args.forall(isValue)
        case _ => false
      }

      private def inlineFunctionInvocations(fi: FunctionInvocation): Expr = {
        import exprOps._
        val (tfd, args) = (fi.tfd, fi.args)

        val isSynthetic = tfd.fd.flags contains Synthetic
        val isOpaqueOrExtern = tfd.fd.flags exists (x => x == Opaque || x == Extern)
        val hasInlineFlag = tfd.fd.flags contains Inline
        val hasInlineOnceFlag = tfd.fd.flags contains InlineOnce

        def willInline = hasInlineFlag || (hasInlineOnceFlag && !inlinedOnce.contains(tfd.id))

        if (!willInline) return fi

        val specced = BodyWithSpecs(tfd.fullBody)
        // simple path for inlining when all arguments are values, and the function's body doesn't contain other function invocations
        if (specced.specs.isEmpty && args.forall(isValue) && !exprOps.containsFunctionCalls(tfd.fullBody) && !isSynthetic && !isOpaqueOrExtern) {
          annotated(exprOps.replaceFromSymbols(tfd.params.zip(args).toMap, exprOps.freshenLocals(tfd.fullBody)), DropVCs)
        } else {
          val pre = specced.specs.filter(spec => spec.kind == LetKind || spec.kind == PreconditionKind)
          val n = pre.count(_.kind == PreconditionKind)
          def addPreconditionAssertions(e: Expr): Expr = {
            pre.foldRight((e, n)) {
              case (spec @ LetInSpec(vd, e0), (acc, i)) => (Let(vd, annotated(e0, DropVCs), acc).setPos(fi), i)
              case (spec @ Precondition(cond), (acc, i)) =>
                val num = if (n == 1) "" else s" ($i/$n)"
                (
                  Assert(annotated(cond.setPos(fi), DropVCs), Some(s"Inlined precondition$num of " + tfd.id.asString), acc).setPos(fi),
                  i-1
                )
              case (spec, (acc,i)) => context.reporter.fatalError(f"In addPreconditionAssertions, I did not expect spec that is not LetInSpec or Precondition; I got the following spec: ${spec.toString}")
            }._1
          }

          val post = specced.getSpec(PostconditionKind)
          def addPostconditionAssumption(e: Expr): Expr = post.map(_.expr) match {
            // We can't assume the post on @synthetic methods as it won't be checked anywhere.
            // It is thus inlined into an assertion here.
            case Some(Lambda(Seq(vd), post)) if isSynthetic =>
              val err = Some("Inlined postcondition of " + tfd.id.name)
              Let(vd, e,
                  Assert(annotated(post, DropVCs), err, vd.toVariable.copiedFrom(fi)
              ).copiedFrom(fi)).copiedFrom(fi)
            case Some(Lambda(Seq(vd), post)) =>
              Let(vd, e, Assume(annotated(post, DropVCs), vd.toVariable.copiedFrom(fi)).copiedFrom(fi)).copiedFrom(fi)
            case _ => e
          }

          val (argBinders, inlined) = specced.bodyOpt match {
            case Some(body) if !isOpaqueOrExtern =>
              // We need to keep the body as-is for `@synthetic` methods, such as
              // `copy` or implicit conversions for implicit classes, in order to
              // later on check that the class invariant is valid.
              // Note: the body local variables and the parameters are not freshened here
              val theBody =
                if (isSynthetic) body
                else annotated(body, DropVCs).setPos(fi)
              val decorated = addPreconditionAssertions(addPostconditionAssumption(theBody))
              (tfd.params, decorated)
            case Some(_) =>
              val argBinders = tfd.params.map(_.freshen)
              val replMap = tfd.params.zip(argBinders.map(_.toVariable)).toMap
              val decorated = addPreconditionAssertions(addPostconditionAssumption(fi.copy(args = argBinders.map(_.toVariable))))
              val repled = exprOps.replaceFromSymbols(replMap, decorated)
              (argBinders, repled)
            case None => context.reporter.fatalError("In FunctionInlining, all functions should have bodies thanks to ChooseEncoder running before.")
          }

          exprOps.preTraversal {
            // Set the position of all occurrences of parameters to the position of their argument
            // For other expressions, we set the position to the call site
            case v: Variable =>
              val ix = argBinders.indexWhere(_.id == v.id)
              if (ix >= 0) {
                // An `argBinder`
                v.setPos(argBinders(ix))
              } else {
                // Some local variable
                v.setPos(fi)
              }
            case e => e.setPos(fi)
          }(inlined)
          val result = (argBinders zip args).foldRight(inlined) {
            case ((vd, e), body) => let(vd.copiedFrom(e), e, body).setPos(fi)
          }
          val freshened = exprOps.freshenLocals(result).copiedFrom(fi)

          val inliner = new Inliner(if (hasInlineOnceFlag) inlinedOnce + tfd.id else inlinedOnce)
          inliner.transform(freshened)
        }
      }
    }

    if ((fd.flags contains Synthetic) && (fd.flags contains Inline)) (None, ())
    else (Some(identity.transform(fd.copy(
      fullBody = new Inliner().transform(fd.fullBody),
      flags = fd.flags filterNot (f => f == Inline || f == InlineOnce)
    ))), ())
  }

  override protected def extractSymbols(context: TransformerContext, symbols: s.Symbols): (t.Symbols, AllSummaries) = {
    for (fd <- symbols.functions.values) {
      val hasInlineFlag = fd.flags contains Inline
      val hasInlineOnceFlag = fd.flags contains InlineOnce
      val isOpaqueOrExtern = fd.flags exists (x => x == Opaque || x == Extern)

      if (hasInlineFlag && hasInlineOnceFlag) {
        throw MalformedStainlessCode(fd, "Can't annotate a function with both @inline and @inlineOnce")
      }

      if (hasInlineFlag && context.transitivelyCalls(fd, fd)) {
        throw MalformedStainlessCode(fd, "Can't inline recursive function, use @inlineOnce instead")
      }

      if (hasInlineFlag && isOpaqueOrExtern) {
        throw MalformedStainlessCode(fd, "Can't inline opaque or extern function, use @inlineOnce instead")
      }

      if (hasInlineFlag && exprOps.BodyWithSpecs(fd.fullBody).bodyOpt.isEmpty) {
        throw MalformedStainlessCode(fd, "Inlining function with empty body: not supported, use @inlineOnce instead")
      }
    }

    val (newSymbols, sum) = super.extractSymbols(context, symbols)

    val inlinedOnceFuns = symbols.functions.values.filter(_.flags contains InlineOnce).map(_.id).toSet

    def isCandidate(id: Identifier): Boolean =
      (inlinedOnceFuns contains id) && (symbols.getFunction(id).flags contains Synthetic)

    def isPrunable(id: Identifier): Boolean =
      isCandidate(id) && newSymbols.transitiveCallers(id).forall(isCandidate)

    (t.NoSymbols
      .withSorts(newSymbols.sorts.values.toSeq)
      .withFunctions(newSymbols.functions.values.filterNot(fd => isPrunable(fd.id)).toSeq), sum)
  }
}

object FunctionInlining {
  def apply(ts: Trees, tt: trace.Trees)(using inox.Context): ExtractionPipeline {
    val s: ts.type
    val t: tt.type
  } = {
    class Impl(override val s: ts.type, override val t: tt.type) extends FunctionInlining(s, t)
    new Impl(ts, tt)
  }
}
