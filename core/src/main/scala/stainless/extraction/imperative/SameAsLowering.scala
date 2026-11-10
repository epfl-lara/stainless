/* Copyright 2009-2026 EPFL, Lausanne */

package stainless
package extraction
package imperative

/** Lowers the `sameAs` construct of observationally pure functions.
  *
  * The frontend only accepts `sameAs(f(x, ..., z))` as a top-level conjunct of a postcondition, applied to the
  * result (see `IsObservationallyPure`). Each such conjunct `sameAs(f(x, ..., z))(res)` is replaced by 
  * `res == f(old(x), ..., old(z)))`. This ensures that
  * the pure reference value is computed in the pre-state, before the function updated its
  * internally mutable fields. The `IsObservationallyPure` flag is kept on the function.
  *
  * This runs first in both imperative pipelines, so that the existing elimination of `old` on
  * parameters (in `AntiAliasing`/`ImperativeCodeElimination`, or `EffectElaboration`) applies.
  * Local functions are lowered with their own parameters only.
  *
  * The argument of `sameAs` must be a call to a function annotated with `@pure`: this is checked
  * here, since the reference call is no longer distinguishable from user code after lowering.
  * The purity of the callee itself is enforced by the `EffectsChecker`, as for any `@pure` function.
  */
trait SameAsLowering extends ExtractionPipeline {
  val s: Trees
  val t: s.type
  import s._

  override def extract(symbols: s.Symbols): (t.Symbols, ExtractionSummary) = {
    val newSymbols = NoSymbols
      .withFunctions(symbols.functions.values.map(lowerFunction(_)(using symbols)).toSeq)
      .withClasses(symbols.classes.values.toSeq)
      .withSorts(symbols.sorts.values.toSeq)
      .withTypeDefs(symbols.typeDefs.values.toSeq)
    (newSymbols, ExtractionSummary.NoSummary)
  }

  override def invalidate(id: Identifier): Unit = ()

  private def lowerFunction(fd: FunDef)(using symbols: s.Symbols): FunDef = {
    if (!containsSameAs(fd.fullBody)) fd
    else {
      checkReferenceCalls(fd)
      val newFullBody = lowerSpecs(fd.params, LocalLowering.transform(fd.fullBody))
      exprOps.preTraversal {
        case sa: SameAs =>
          throw MalformedStainlessCode(sa,
            "`sameAs` can only appear as a top-level conjunct of a postcondition, applied to the result")
        case _ => ()
      }(newFullBody)
      fd.copy(fullBody = newFullBody).copiedFrom(fd)
    }
  }

  private def containsSameAs(e: Expr): Boolean = exprOps.exists(_.isInstanceOf[SameAs])(e)

  /** Checks that every `sameAs(e)` in `fd` (including in its local functions) has as `e` a call to a function
    * annotated `@pure`. That the callee indeed has no effects is then enforced by the `EffectsChecker`.
    */
  private def checkReferenceCalls(fd: FunDef)(using symbols: s.Symbols): Unit = {
    lazy val localFlags: Map[Identifier, Seq[Flag]] = exprOps.collect[(Identifier, Seq[Flag])] {
      case LetRec(lfds, _) => lfds.map(lfd => lfd.id -> lfd.flags).toSet
      case _ => Set.empty
    }(fd.fullBody).toMap

    exprOps.preTraversal {
      case sa @ SameAs(call) =>
        val (calleeId, calleeFlags) = call match {
          case FunctionInvocation(id, _, _) => (id, symbols.getFunction(id).flags)
          case ApplyLetRec(id, _, _, _, _) => (id, localFlags.getOrElse(id, Seq.empty))
          case _ => throw MalformedStainlessCode(sa, "`sameAs` must be applied to a function call, e.g. `sameAs(f(x))`")
        }
        if (!calleeFlags.contains(IsPure))
          throw ImperativeEliminationException(sa,
            s"`sameAs` must be applied to a call to a function annotated with @pure, but ${calleeId.asString} is not")
      case _ => ()
    }(fd.fullBody)
  }

  /** Lowers the `sameAs` conjuncts of the postcondition of a function with the given parameters. */
  private def lowerSpecs(params: Seq[ValDef], fullBody: Expr): Expr = {
    val specced = exprOps.BodyWithSpecs(fullBody)
    val newSpecs = specced.specs.map {
      case post @ exprOps.Postcondition(lam @ Lambda(Seq(res), postBody)) =>
        val newPostBody = exprOps.postMap {
          case app @ Application(SameAs(e), Seq(v: Variable)) if v.id == res.id =>
            Some(Equals(v, inPreState(params, e)).copiedFrom(app))
          case _ => None
        }(postBody)
        exprOps.Postcondition(Lambda(Seq(res), newPostBody).copiedFrom(lam)).setPos(post)
      case spec => spec
    }
    specced.copy(specs = newSpecs).reconstructed
  }

  /** Wraps every occurrence of the given parameters in `e` with `old(...)`, leaving existing `old`s untouched. */
  private def inPreState(params: Seq[ValDef], e: Expr): Expr = {
    val ids = params.map(_.id).toSet
    object ToPreState extends ConcreteStainlessSelfTreeTransformer {
      override def transform(e: Expr): Expr = e match {
        case o: Old => o
        case v: Variable if ids(v.id) => Old(v).copiedFrom(v)
        case _ => super.transform(e)
      }
    }
    ToPreState.transform(e)
  }

  /** Lowers the postconditions of nested local functions. */
  private object LocalLowering extends ConcreteStainlessSelfTreeTransformer {
    override def transform(e: Expr): Expr = e match {
      case LetRec(fds, body) =>
        val newFds = fds.map { lfd =>
          lfd.copy(fullBody = lowerSpecs(lfd.params, transform(lfd.fullBody))).copiedFrom(lfd)
        }
        LetRec(newFds, transform(body)).copiedFrom(e)
      case _ => super.transform(e)
    }
  }
}

object SameAsLowering {
  def apply(trees: Trees)(using inox.Context): ExtractionPipeline {
    val s: trees.type
    val t: trees.type
  } = {
    class Impl(override val s: trees.type, override val t: trees.type)(using override val context: inox.Context)
      extends SameAsLowering
    new Impl(trees, trees)
  }
}
