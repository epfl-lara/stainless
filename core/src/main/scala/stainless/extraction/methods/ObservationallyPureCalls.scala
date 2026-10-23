/* Copyright 2009-2026 EPFL, Lausanne */

package stainless
package extraction
package methods

/** Replaces calls to observationally pure methods by their pure reference function.
  *
  * An observationally pure method `m` has a postcondition with a top-level conjunct `sameAs(f(e1, ..., en))`,
  * which is verified (after `imperative.SameAsLowering`) as `res == f(e1, ..., en)` evaluated in the pre-state.
  * Hence, for verification purposes, a call `o.m(a1, ..., ak)` is replaced by
  * {{{
  *   val r = o; val p1 = a1; ...; val pk = ak
  *   assert(pre_m(r, p1, ..., pk))
  *   f(e1, ..., en)[this := r, params := p]
  * }}}
  * (the receiver is only bound if `this` is used by the replacement or if it is not a variable),
  * which has no effects: callers can thus use `m` as a pure function (e.g. as argument of `map`), although
  * `m` mutates its `@internallyMutable` fields at runtime. The method `m` itself is kept, and verified as usual.
  *
  * Calls on `this` from methods of the same class that can access its internally mutable fields (observationally
  * pure, ghost, or invariant methods) are not replaced, as these methods may observe the updated fields.
  *
  * For the replacement to be sound:
  *  - `f` must be defined outside of classes with `@internallyMutable` fields;
  *  - `m` must not be overridable, so that calls to `m` cannot dispatch to another implementation: `m` and its
  *    class must be concrete (concrete classes cannot be extended in Stainless).
  *
  * This runs before `MethodLifting`, while methods are still attached to their class and `this` is explicit.
  */
trait ObservationallyPureCalls extends ExtractionPipeline {
  val s: Trees
  val t: s.type
  import s._

  override def extract(symbols: s.Symbols): (t.Symbols, ExtractionSummary) = {
    given s.Symbols = symbols

    val imClasses: Set[Identifier] = symbols.classes.values.collect {
      case cd if cd.fields.exists(_.flags.contains(IsInternallyMutable)) => cd.id
    }.toSet

    symbols.functions.values.foreach(checkReferenceFunction(_, imClasses))

    // Observationally pure methods, with their `sameAs` reference call
    val obsPureMethods: Map[Identifier, (FunDef, Expr)] = symbols.functions.values.flatMap { fd =>
      if (!fd.flags.contains(IsObservationallyPure) || fd.flags.forall { case IsMethodOf(_) => false; case _ => true }) None
      else referenceCall(fd).map { ref =>
        checkNotOverridable(fd)
        fd.id -> (fd, ref)
      }
    }.toMap

    if (obsPureMethods.isEmpty) (symbols, ExtractionSummary.NoSummary)
    else {
      val newSymbols = NoSymbols
        .withFunctions(symbols.functions.values.map(replaceCalls(_, obsPureMethods)).toSeq)
        .withClasses(symbols.classes.values.toSeq)
        .withSorts(symbols.sorts.values.toSeq)
        .withTypeDefs(symbols.typeDefs.values.toSeq)
      (newSymbols, ExtractionSummary.NoSummary)
    }
  }

  override def invalidate(id: Identifier): Unit = ()

  private def classOf(fd: FunDef): Option[Identifier] = fd.flags.collectFirst { case IsMethodOf(cid) => cid }

  /** The argument of the `sameAs` conjunct in the postcondition of `fd`, if any. */
  private def referenceCall(fd: FunDef): Option[Expr] = {
    exprOps.BodyWithSpecs(fd.fullBody).getSpec(exprOps.PostconditionKind).flatMap {
      case exprOps.Postcondition(Lambda(Seq(res), post)) =>
        exprOps.collect[Expr] {
          case Application(SameAs(e), Seq(v: Variable)) if v.id == res.id => Set(e)
          case _ => Set.empty
        }(post).headOption
    }
  }

  /** The function referenced in `sameAs` must be defined outside of classes with internally mutable fields. */
  private def checkReferenceFunction(fd: FunDef, imClasses: Set[Identifier])(using symbols: s.Symbols): Unit = {
    exprOps.preTraversal {
      case sa @ SameAs(MethodInvocation(_, id, _, _)) =>
        symbols.lookupFunction(id).flatMap(classOf).filter(imClasses).foreach { cid =>
          throw MethodsException(sa,
            s"The function in `sameAs` must be defined outside of classes with @internallyMutable fields, " +
            s"but ${id.asString} is a method of ${cid.asString}")
        }
      case _ => ()
    }(fd.fullBody)
  }

  /** Calls to an observationally pure method can only be replaced if they cannot dispatch to an override. */
  private def checkNotOverridable(fd: FunDef)(using symbols: s.Symbols): Unit = {
    val cd = symbols.getClass(classOf(fd).get)
    if (fd.isAbstract || cd.isAbstract)
      throw MethodsException(fd,
        s"Observationally pure method ${fd.id.asString} must not be overridable: it must be concrete, " +
        s"and its class ${cd.id.asString} must be concrete (not abstract or a trait)")
  }

  private def isAllowedMethod(fd: FunDef): Boolean = fd.flags.exists {
    case IsObservationallyPure | IsInvariant | Ghost => true
    case _ => false
  }

  private def isThis(e: Expr): Boolean = e match {
    case _: This => true
    case Annotated(e, _) => isThis(e)
    case _ => false
  }

  private def replaceCalls(fd: FunDef, obsPureMethods: Map[Identifier, (FunDef, Expr)])(using symbols: s.Symbols): FunDef = {
    // Calls on `this` to methods of this class are kept in methods that may observe its internally mutable fields
    val keptClass: Option[Identifier] = if (isAllowedMethod(fd)) classOf(fd) else None

    val newBody = exprOps.postMap {
      case mi @ MethodInvocation(recv, id, tps, args)
          if obsPureMethods.contains(id) && !(isThis(recv) && keptClass == classOf(obsPureMethods(id)._1)) =>
        val (m, ref) = obsPureMethods(id)
        Some(replacement(mi, recv, tps, args, m, ref))
      case _ => None
    }(fd.fullBody)

    if (newBody eq fd.fullBody) fd else fd.copy(fullBody = newBody).copiedFrom(fd)
  }

  private def replacement(call: Expr, recv: Expr, tps: Seq[Type], args: Seq[Expr], m: FunDef, ref: Expr)
                         (using symbols: s.Symbols): Expr = {
    val cd = symbols.getClass(classOf(m).get)
    val classTps: Seq[Type] = recv.getType match {
      case ct: ClassType if ct.id == cd.id => ct.tps
      case _ => cd.typeArgs
    }
    val tpMap: Map[TypeParameter, Type] =
      ((cd.typeArgs zip classTps) ++ (m.typeArgs zip tps)).toMap

    val recvVd = ValDef.fresh("recv", recv.getType).copiedFrom(call)
    val paramVds = m.params.zip(args).map { case (p, a) =>
      ValDef.fresh(p.id.name, typeOps.instantiateType(p.tpe, tpMap)).copiedFrom(a)
    }
    val subst: Map[Identifier, Expr] = m.params.map(_.id).zip(paramVds.map(_.toVariable)).toMap

    def instantiate(e: Expr): Expr = typeOps.instantiateType(exprOps.postMap {
      case _: This => Some(recvVd.toVariable)
      case v: Variable => subst.get(v.id)
      case _ => None
    }(e), tpMap)

    val pre = exprOps.BodyWithSpecs(m.fullBody).getSpec(exprOps.PreconditionKind).map(p => instantiate(p.expr))
    val refCall = instantiate(ref).copiedFrom(call)
    val checked = pre match {
      case Some(p) =>
        Assert(p, Some(s"Precondition of observationally pure method ${m.id.asString}"), refCall).copiedFrom(call)
      case None => refCall
    }
    // When `this` is not used by the replacement, the receiver is not bound if it is a variable (so that, e.g.,
    // `x => m(x)` becomes `x => f(x)`, which does not capture the possibly mutable `m`)
    val usesThis = exprOps.exists(_.isInstanceOf[This])(ref) ||
      exprOps.BodyWithSpecs(m.fullBody).getSpec(exprOps.PreconditionKind).exists(p => exprOps.exists(_.isInstanceOf[This])(p.expr))
    val bindRecv = usesThis || !(recv.isInstanceOf[Variable] || isThis(recv))
    val bindings = (if (bindRecv) Seq(recvVd -> recv) else Seq()) ++ paramVds.zip(args)
    bindings.foldRight(checked) {
      case ((vd, e), body) => Let(vd, e, body).copiedFrom(call)
    }
  }
}

object ObservationallyPureCalls {
  def apply(trees: Trees)(using inox.Context): ExtractionPipeline {
    val s: trees.type
    val t: trees.type
  } = {
    class Impl(override val s: trees.type, override val t: trees.type)(using override val context: inox.Context)
      extends ObservationallyPureCalls
    new Impl(trees, trees)
  }
}
