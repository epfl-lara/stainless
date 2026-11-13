/* Copyright 2009-2026 EPFL, Lausanne */

package stainless
package extraction
package imperative

/** Lowers the `sameAs` construct of observationally equivalent functions.
  *
  * The frontend only accepts `sameAs(f(args))` as a top-level conjunct of a postcondition, applied to the
  * result, where `f` is a top-level function (see `IsObservationallyEquivalent`). Its only effects are thus on
  * its arguments. Each such conjunct `sameAs(f(x, y))(res)`, where `x` has a mutable type and `y` does not, is
  * replaced by
  * {{{
  *   @ghost val x1 = freshCopy(old(x))
  *   @ghost val r = f(x1, old(y))
  *   res == r && x == x1
  * }}}
  * that is, `f` is run in the pre-state, on a copy of the mutable arguments, and must return the same result
  * and leave the mutable arguments in the same state as the function. Without mutable arguments, this is
  * `res == f(old(x), ..., old(z))`. The `IsObservationallyEquivalent` flag is kept on the function.
  *
  * The mutable arguments of `f` must be distinct parameters of the function (recorded in the flag by the
  * frontend, so `this` is excluded). Their types must not contain arrays, whose equality is not structural.
  * `EffectsChecker` then ensures that the function only has effects on these parameters and on
  * `@internallyMutable` fields.
  *
  * This runs first in both imperative pipelines, so that the existing elimination of `old` on
  * parameters (in `AntiAliasing`/`ImperativeCodeElimination`) applies. Local functions are lowered with
  * their own parameters only. `sameAs` and `@internallyMutable` are not supported with `--full-imperative`,
  * which does not run `EffectsChecker`.
  */
trait SameAsLowering extends ExtractionPipeline {
  val s: Trees
  val t: s.type
  import s._

  override def extract(symbols: s.Symbols): (t.Symbols, ExtractionSummary) = {
    if (context.options.findOptionOrDefault(optFullImperative)) checkNotUsed(symbols)
    val newSymbols = NoSymbols
      .withFunctions(symbols.functions.values.map(lowerFunction(_)(using symbols)).toSeq)
      .withClasses(symbols.classes.values.toSeq)
      .withSorts(symbols.sorts.values.toSeq)
      .withTypeDefs(symbols.typeDefs.values.toSeq)
    (newSymbols, ExtractionSummary.NoSummary)
  }

  override def invalidate(id: Identifier): Unit = ()

  private def checkNotUsed(symbols: s.Symbols): Unit = {
    val message = "@internallyMutable fields and `sameAs` are not supported with --full-imperative"
    symbols.classes.values.flatMap(_.fields).find(_.flags.contains(IsInternallyMutable)).foreach { vd =>
      throw ImperativeEliminationException(vd, message)
    }
    symbols.functions.values.foreach { fd =>
      exprOps.preTraversal {
        case sa: SameAs => throw ImperativeEliminationException(sa, message)
        case _ => ()
      }(fd.fullBody)
    }
  }

  private def lowerFunction(fd: FunDef)(using symbols: s.Symbols): FunDef = {
    if (!containsSameAs(fd.fullBody)) fd
    else {
      checkReferenceCalls(fd)
      val newFullBody = lowerSpecs(fd.params, sameAsParams(fd.flags), LocalLowering().transform(fd.fullBody))
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

  /** The parameters that appear as arguments of the `sameAs` reference call (see `IsObservationallyEquivalent`). */
  private def sameAsParams(flags: Seq[Flag]): Set[Identifier] =
    flags.collectFirst { case IsObservationallyEquivalent(ids) => ids.toSet }.getOrElse(Set.empty)

  /** Checks that every `sameAs(e)` in `fd` (including in its local functions) has as `e` a call to a top-level
    * function (already checked by the frontend).
    */
  private def checkReferenceCalls(fd: FunDef): Unit = {
    exprOps.preTraversal {
      case SameAs(_: FunctionInvocation) => ()
      case sa: SameAs =>
        throw MalformedStainlessCode(sa, "`sameAs` must be applied to a call to a top-level function, e.g. `sameAs(f(x))`")
      case _ => ()
    }(fd.fullBody)
  }

  /** Lowers the `sameAs` conjuncts of the postcondition of a function with the given parameters. */
  private def lowerSpecs(params: Seq[ValDef], sameAsParams: Set[Identifier], fullBody: Expr)
                        (using symbols: s.Symbols): Expr = {
    val specced = exprOps.BodyWithSpecs(fullBody)
    val newSpecs = specced.specs.map {
      case post @ exprOps.Postcondition(lam @ Lambda(Seq(res), postBody)) =>
        val newPostBody = exprOps.postMap {
          case app @ Application(SameAs(call: FunctionInvocation), Seq(v: Variable)) if v.id == res.id =>
            Some(lowerSameAs(params, sameAsParams, v, call).copiedFrom(app))
          case _ => None
        }(postBody)
        exprOps.Postcondition(Lambda(Seq(res), newPostBody).copiedFrom(lam)).setPos(post)
      case spec => spec
    }
    specced.copy(specs = newSpecs).reconstructed
  }

  /** Lowers `sameAs(call)(res)`, see the documentation of this phase. */
  private def lowerSameAs(params: Seq[ValDef], sameAsParams: Set[Identifier], res: Variable, call: FunctionInvocation)
                         (using symbols: s.Symbols): Expr = {
    val mutableArgs: Seq[Variable] = call.args.filter(arg => symbols.isMutableType(arg.getType)).map {
      case v: Variable if sameAsParams(v.id) =>
        if (mayContainArray(v.getType, Set()))
          throw ImperativeEliminationException(v,
            s"Mutable arguments of the function in `sameAs` cannot contain arrays, " +
            s"but ${v.asString} has type ${v.getType.asString}")
        v
      case arg =>
        throw ImperativeEliminationException(arg,
          s"Mutable arguments of the function in `sameAs` must be parameters of the function, " +
          s"but ${arg.asString} is not")
    }
    mutableArgs.diff(mutableArgs.distinct).headOption.foreach { v =>
      throw ImperativeEliminationException(v,
        s"Mutable arguments of the function in `sameAs` must be distinct, but ${v.asString} is passed twice")
    }

    if (mutableArgs.isEmpty) Equals(res, inPreState(params, call).copiedFrom(call))
    else {
      val copies: Map[Variable, ValDef] = mutableArgs.map { v =>
        v -> ValDef(FreshIdentifier(v.id.name + "Copy"), v.getType, Seq(Ghost)).copiedFrom(v)
      }.toMap
      val newArgs = call.args.map {
        case v: Variable if copies.contains(v) => copies(v).toVariable
        case arg => inPreState(params, arg)
      }
      val ref = ValDef(FreshIdentifier("ref"), res.getType, Seq(Ghost)).copiedFrom(call)
      val body = And(Equals(res, ref.toVariable) +: mutableArgs.map(v => Equals(v, copies(v).toVariable)))
      val withRef = Let(ref, FunctionInvocation(call.id, call.tps, newArgs).copiedFrom(call), body)
      mutableArgs.foldRight(withRef: Expr) { (v, e) =>
        Let(copies(v), FreshCopy(Old(v).copiedFrom(v)).copiedFrom(v), e)
      }
    }
  }

  /** Whether values of type `tpe` may contain an array (or a mutable map), whose equality is not structural. */
  private def mayContainArray(tpe: Type, visited: Set[Identifier])(using symbols: s.Symbols): Boolean = tpe match {
    case _: ArrayType | _: MutableMapType => true
    case tp: TypeParameter => tp.flags.contains(IsMutable)
    case ct: ClassType =>
      !visited(ct.id) && ct.tcd.fields.exists(vd => mayContainArray(vd.getType, visited + ct.id))
    case adt: ADTType =>
      !visited(adt.id) && adt.getSort.constructors.exists(_.fields.exists(vd => mayContainArray(vd.getType, visited + adt.id)))
    // The base type of a RefinementType is hidden inside its ValDef, so the
    // generic NAryType case would not see it (RefinementType deconstructs with no sub-types).
    case RefinementType(vd, _) => mayContainArray(vd.tpe, visited)
    case NAryType(tps, _) => tps.exists(mayContainArray(_, visited))
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
  private class LocalLowering(using symbols: s.Symbols) extends ConcreteStainlessSelfTreeTransformer {
    override def transform(e: Expr): Expr = e match {
      case LetRec(fds, body) =>
        val newFds = fds.map { lfd =>
          lfd.copy(fullBody = lowerSpecs(lfd.params, sameAsParams(lfd.flags), transform(lfd.fullBody))).copiedFrom(lfd)
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
