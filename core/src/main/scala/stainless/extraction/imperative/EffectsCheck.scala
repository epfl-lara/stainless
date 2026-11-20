/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package imperative

class EffectsCheck(override val s: Trees)(override val t: s.type)(using override val context: inox.Context)
  extends oo.CachingPhase
     with SimpleSorts
     with oo.IdentityTypeDefs
     with oo.SimpleClasses
     with EffectsAnalyzer { self =>
  import s._
  import exprOps._

  override protected final val funCache = new ExtractionCache[s.FunDef, (FunctionResult, FunctionSummary)]((fd, context) =>
    getDependencyKey(fd.id)(using context.symbols)
  )
  override protected final val sortCache = new ExtractionCache[s.ADTSort, (SortResult, SortSummary)]((sort, context) =>
    getDependencyKey(sort.id)(using context.symbols)
  )
  override protected final val classCache = new ExtractionCache[s.ClassDef, (ClassResult, ClassSummary)]((cd, context) =>
    getDependencyKey(cd.id)(using context.symbols)
  )

  protected case class TransformerContext()(using override val symbols: Symbols) extends EffectsAnalysis

  override protected def getContext(symbols: Symbols) = TransformerContext()(using symbols)

  override protected type FunctionResult = FunDef
  override protected type FunctionSummary = Unit
  override protected def registerFunctions(symbols: t.Symbols, functions: Seq[t.FunDef]): t.Symbols =
    symbols.withFunctions(functions)

  override protected def extractFunction(analysis: TransformerContext, fd: FunDef): (FunDef, Unit) = {
    import analysis.{given, _}

    if (!isMutableSynthetic(fd.id) && !isAccessor(Outer(fd))) {
      ensureFunction(Outer(fd))(using analysis)
    }

    (fd, ())
  }

  override protected type SortSummary = Unit
  override protected def extractSort(analysis: TransformerContext, sort: ADTSort): (ADTSort, Unit) =
    (sort, ())

  override protected type ClassSummary = Unit
  override protected def extractClass(analysis: TransformerContext, cd: ClassDef): (ClassDef, Unit) = {
    import analysis.given

    cd.fields.foreach(field => TypeChecker().traverse(field.tpe))

    (cd, ())
  }

  override protected def combineSummaries(allSummaries: AllSummaries): ExtractionSummary =
    ExtractionSummary.NoSummary

  private def isAccessor(fd: FunAbstraction): Boolean =
    fd.flags.exists(_.name == "accessor")

  private def isMutableSynthetic(id: Identifier)(using symbols: Symbols): Boolean = {
    val fd = symbols.getFunction(id)

    fd.flags.contains(Synthetic) &&
      !isAccessor(Outer(fd)) &&
      fd.params.exists(vd => symbols.isMutableType(vd.tpe)) &&
      !exprOps.BodyWithSpecs(fd.fullBody).bodyOpt.forall(isExpressionFresh)
  }

  private class TypeChecker(using symbols: Symbols) extends ConcreteSelfTreeTraverser {
    import symbols.isMutableType

    private def ensureTypeArguments(tree: Tree, kind: String, tparams: Seq[TypeParameterDef], tps: Seq[Type]): Unit =
      tparams.zip(tps).foreach { case (tdef, instance) =>
        if (isMutableType(instance) && !tdef.flags.contains(IsMutable)) {
          throw ImperativeEliminationException(tree,
            s"Cannot instantiate a non-mutable $kind type parameter ${tdef.asString} with a mutable type ${instance.asString}")
        }
      }

    override def traverse(tpe: Type): Unit = {
      tpe match {
        case adt: ADTType => ensureTypeArguments(tpe, "ADT", adt.getSort.definition.tparams, adt.tps)
        case ct: ClassType => ensureTypeArguments(tpe, "class", ct.tcd.cd.tparams, ct.tps)
        case SetType(element) if isMutableType(element) =>
          throw ImperativeEliminationException(tpe, s"Cannot instantiate a set ${tpe.asString} with a mutable type ${element.asString}")
        case BagType(element) if isMutableType(element) =>
          throw ImperativeEliminationException(tpe, s"Cannot instantiate a bag ${tpe.asString} with a mutable type ${element.asString}")
        case MapType(from, _) if isMutableType(from) =>
          throw ImperativeEliminationException(tpe, s"Cannot instantiate a map ${tpe.asString} with a mutable key type ${from.asString}")
        case MutableMapType(from, _) if isMutableType(from) =>
          throw ImperativeEliminationException(tpe, s"Cannot instantiate a mutable map ${tpe.asString} with a mutable key type ${from.asString}")
        case _ =>
      }

      super.traverse(tpe)
    }
  }

  private def ensureFunction(fd: FunAbstraction)(using analysis: TransformerContext): Unit = {
    import analysis._
    import analysis.symbols.{isMutableType, given}

    def ensureNoMutableStateInVariableType(tpe: Type): Unit = {
      object variableTypeTraverser extends ConcreteSelfTreeTraverser {
        override def traverse(tpe: Type): Unit = tpe match {
          case rt @ RefinementType(refVd, pred) =>
            if (refsToMutable(pred).nonEmpty) {
              throw ImperativeEliminationException(tpe, "Cannot reference a mutable state from a type of a variable")
            }

            ensureNoMutableStateInVariableType(refVd.tpe)
            super.traverse(rt)

          case _ =>
            super.traverse(tpe)
        }
      }

      variableTypeTraverser.traverse(tpe)
    }

    object traverser extends TypeChecker {
      override def traverse(tpe: Type): Unit = {
        tpe match {
          case rt @ RefinementType(_, pred) =>
            val predEffects = effects(pred)
            if (predEffects.nonEmpty) {
              throw ImperativeEliminationException(rt, "Refinement type predicate has effects on: " + predEffects.head.receiver.asString)
            }

          case _ =>
        }

        super.traverse(tpe)
      }

      override def traverse(e: Expr): Unit = e match {
        case LetVar(vd, _, _) =>
          ensureNoMutableStateInVariableType(vd.tpe)
          super.traverse(e)

        case LetRec(fds, body) =>
          fds.foreach(fd => ensureFunction(Inner(fd)))
          traverse(body)

        case lambda @ Lambda(args, body) =>
          if (effects(body).exists(effect => !args.contains(effect.receiver.toVal))) {
            throw ImperativeEliminationException(lambda, "Illegal effects in lambda body")
          }

          super.traverse(lambda)

        case fi: FunctionInvocation if isMutableSynthetic(fi.id) =>
          throw ImperativeEliminationException(fi, s"Cannot call '${fi.id.asString}' on a class with mutable fields")

        case fi @ FunctionInvocation(id, tps, _) =>
          val callee = analysis.symbols.getFunction(id)
          callee.tparams.zip(tps).foreach { case (tp, tpe) =>
            if (isMutableType(tpe) && !tp.flags.contains(IsMutable)) {
              throw ImperativeEliminationException(e,
                s"Cannot instantiate a non-mutable function type parameter ${tp.asString} in ${fi.asString} with the mutable type ${tpe.asString}")
            }
          }

          super.traverse(fi)

        case adt @ ADT(_, tps, _) =>
          adt.getConstructor.sort.definition.tparams.zip(tps).foreach { case (tdef, instance) =>
            if (isMutableType(instance) && !tdef.flags.contains(IsMutable)) {
              throw ImperativeEliminationException(e,
                s"Cannot instantiate a non-mutable ADT constructor type parameter ${tdef.asString} in ${adt.asString} with a mutable type ${instance.asString}")
            }
          }

          super.traverse(adt)

        case LargeArray(_, default, _, _) =>
          if (!isReferentiallyTransparent(default)) {
            throw ImperativeEliminationException(e, s"Cannot use effectfull computations within Array.fill (${default.asString})")
          }

          super.traverse(e)

        case _ =>
          super.traverse(e)
      }
    }

    def ensureMutableField(fd: FunAbstraction): Unit = {
      if (!fd.flags.exists { case IsField(_) => true case _ => false }) {
        return
      }

      if (isMutableType(fd.returnType)) {
        throw ImperativeEliminationException(fd, "A field cannot refer to a mutable object")
      }

      if (effects(fd.fullBody).nonEmpty) {
        throw ImperativeEliminationException(fd, s"A field must be pure, but ${fd.id.asString} has effects: ${effects(fd.fullBody).map(_.asString).mkString(", ")}")
      }
    }

    def ensureNoEffects(tree: Expr, description: String): Unit = {
      val treeEffects = effects(tree)
      if (treeEffects.nonEmpty) {
        throw ImperativeEliminationException(tree, s"$description has effects on: " + treeEffects.head.receiver.asString)
      }
    }

    def ensureEffectsLocations(fd: FunAbstraction): Unit = exprOps.preTraversal {
      case Require(pre, _) =>
        ensureNoEffects(pre, "Precondition")

      case Ensuring(_, post @ Lambda(_, body)) =>
        val bodyEffects = effects(body)
        if (bodyEffects.nonEmpty) {
          throw ImperativeEliminationException(post, "Postcondition has effects on: " + bodyEffects.head.receiver.asString)
        }

        val oldEffects = effects(exprOps.postMap {
          case Old(e) => Some(e)
          case _ => None
        }(body))
        if (oldEffects.nonEmpty) {
          throw ImperativeEliminationException(post, s"Postcondition tries to mutate ${Old(oldEffects.head.receiver).asString}")
        }

      case Decreases(measure, _) =>
        ensureNoEffects(measure, "Decreases")

      case Assert(pred, _, _) =>
        ensureNoEffects(pred, "Assertion")

      case ArrayUpdated(array, index, value) =>
        ensureNoEffects(array, "ArrayUpdated operand")
        ensureNoEffects(index, "ArrayUpdated key")
        ensureNoEffects(value, "ArrayUpdated value")

      case Forall(_, pred) =>
        ensureNoEffects(pred, "Quantifier")

      case While(_, _, invariant, weakInvariant, _) =>
        (invariant.toSeq ++ weakInvariant).foreach(ensureNoEffects(_, "Loop invariant"))

      case MatchExpr(_, cases) =>
        cases.foreach { matchCase =>
          matchCase.optGuard.foreach(ensureNoEffects(_, "Pattern guard"))

          patternOps.preTraversal {
            case pattern: UnapplyPattern =>
              val unapplyEffects = effects(Outer(pattern.getFunction.fd))
              if (unapplyEffects.nonEmpty) {
                throw ImperativeEliminationException(pattern, "Pattern unapply has effects on: " + unapplyEffects.head.receiver.asString)
              }

            case _ =>
          }(matchCase.pattern)
        }

      case Let(vd, value, _) if vd.flags.contains(Lazy) =>
        val valueEffects = effects(value)
        if (valueEffects.nonEmpty) {
          throw ImperativeEliminationException(value, "Stainless does not support effects in lazy val's on: " + valueEffects.head.receiver.asString)
        }

      case And(exprs) =>
        exprs.foreach(ensureNoEffects(_, "Operand of '&&'"))

      case Or(exprs) =>
        exprs.foreach(ensureNoEffects(_, "Operand of '||'"))

      case Implies(lhs, rhs) =>
        ensureNoEffects(lhs, "Left-hand-side of '==>'")
        ensureNoEffects(rhs, "Right-hand-side of '==>'")

      case _ =>
    }(fd.fullBody)

    def resolveCallsToImpure(fd: FunAbstraction): Seq[(Identifier, Set[Variable])] =
      exprOps.collect {
        case FunctionInvocation(id, _, args) =>
          val callee = analysis.symbols.getFunction(id)
          val calleeEffects = effects(callee)
          if (calleeEffects.isEmpty) {
            Set.empty[(Identifier, Set[Variable])]
          } else {
            val indices = calleeEffects.map(effect => callee.params.indexWhere(_.id == effect.receiver.id)).filter(_ >= 0)
            val affectedParams = indices.flatMap(index => exprOps.variablesOf(args(index)) & fd.params.map(_.toVariable).toSet)
            Set((id, affectedParams))
          }

        case _ =>
          Set.empty[(Identifier, Set[Variable])]
      }(fd.fullBody).groupMapReduce(_._1)(_._2)(_ ++ _).toSeq.sortBy(_._1)

    def ensureEnforcedPurity(fd: FunAbstraction, functionEffects: Set[Effect], callsToImpure: Seq[(Identifier, Set[Variable])]): Unit = {
      val isPure = fd.flags.contains(IsPure)
      val isObservationallyPure = fd.flags.contains(IsObservationallyPure)
      val isInvariant = fd.flags.contains(IsInvariant)

      if ((isPure || isInvariant) && functionEffects.nonEmpty) {
        val name = if (isInvariant) "the invariant" else fd.id.asString
        val head = Seq(if (isInvariant) "Invariants cannot have side-effects" else "Functions marked @pure cannot have side-effects")
        val externs = callsToImpure.filter { case (id, _) => analysis.symbols.getFunction(id).flags.contains(Extern) }.map(_._1).toSet
        val callsHint =
          if (callsToImpure.isEmpty) Seq.empty[String]
          else Seq(s"Hint: $name calls the following impure functions:") ++ callsToImpure.map { case (id, _) =>
            val extra = if (externs(id)) " (an @extern function)" else ""
            s"  -${id.asString}$extra"
          }
        val externHint =
          if (externs.isEmpty) Seq.empty
          else Seq("Hint: @extern functions taking mutable types are considered as impure, unless annotated with @pure")

        throw ImperativeEliminationException(fd, (head ++ callsHint ++ externHint).mkString("\n"))
      }

      if (!isObservationallyPure) {
        return
      }

      val illegal = functionEffects.filterNot { effect =>
        effect.path.toSeq.headOption match {
          case Some(ClassFieldAccessor(field)) => field.flags.contains(IsInternallyMutable)
          case _ => false
        }
      }

      if (illegal.nonEmpty) {
        val targets = illegal.map(effect => effect.receiver.asString + effect.path.asString).toSeq.sorted.mkString(", ")
        throw ImperativeEliminationException(fd,
          s"Observationally pure functions (with a `sameAs` postcondition) can only have side-effects on " +
          s"@internallyMutable fields, but ${fd.id.asString} has side-effects on: $targets")
      }
    }

    def ensurePureParameters(fd: FunAbstraction, functionEffects: Set[Effect], callsToImpure: Seq[(Identifier, Set[Variable])]): Unit = {
      val mutatedPure = functionEffects
        .filter(_.receiver.flags.contains(IsPure))
        .map(_.receiver)
        .toSeq
        .sortBy(v => fd.params.indexWhere(_.id == v))

      if (mutatedPure.isEmpty) {
        return
      }

      val head = Seq(s"Function `${fd.id.asString}` has effect on the following @pure parameters:", mutatedPure.map(_.id.asString).mkString("  -", ", ", ""))
      val externs = callsToImpure.filter { case (id, _) => analysis.symbols.getFunction(id).flags.contains(Extern) }.map(_._1).toSet
      val callsHint = mutatedPure.flatMap { v =>
        val callees = callsToImpure.filter(_._2(v)).map(_._1)
        if (callees.isEmpty) Seq.empty
        else Seq(s"Hint: ${v.id.asString} is modified by the calls to the following functions:") ++ callees.map { id =>
          val extra = if (externs(id)) " (an @extern function)" else ""
          s"  -${id.asString}$extra"
        }
      }
      val externHint =
        if (externs.isEmpty) Seq.empty
        else Seq("Hint: @extern functions taking mutable types are considered as impure, unless annotated with @pure")

      throw ImperativeEliminationException(fd, (head ++ callsHint ++ externHint).mkString("\n"))
    }

    def ensurePurity(fd: FunAbstraction): Unit = {
      val functionEffects = effects(fd.fullBody)
      val callsToImpure = resolveCallsToImpure(fd)

      ensureEnforcedPurity(fd, functionEffects, callsToImpure)
      ensurePureParameters(fd, functionEffects, callsToImpure)
    }

    ensureMutableField(fd)
    ensureEffectsLocations(fd)
    ensurePurity(fd)

    traverser.traverse(fd.fullBody)
    fd.params.foreach(param => traverser.traverse(param.tpe))
  }
}

object EffectsCheck extends ExtractionPipelineCreator {
  override val name: String = "EffectsCheck"

  def apply(trees: Trees)(using inox.Context): ExtractionPipeline {
    val s: trees.type
    val t: trees.type
  } = {
    class Impl(override val s: trees.type, override val t: trees.type) extends EffectsCheck(s)(t)
    new Impl(trees, trees)
  }
}
