/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package imperative

trait AssignmentRewrites extends HeapApproximationAnalyses {
  import s._

  /** Makes `holder` take `value` again after a mutation, when `condition` holds. */
  case class Refresh(holder: Variable, value: Expr, condition: Expr)

  /** A variable followed by the steps of a selection such as `x.f(i)._1`. */
  case class VariablePath(root: Variable, accessors: Seq[HeapAccessor]) {
    /** Whether `dependency` is exactly this path. */
    def isPathOf(dependency: HeapTargetDependency): Boolean =
      dependency.variable == root.id && dependency.accessors == accessors

    /** Whether `dependency` starts with this path. */
    def isPrefixOf(dependency: HeapTargetDependency): Boolean =
      dependency.variable == root.id && dependency.accessors.startsWith(accessors)
  }

  object VariablePath {
    /** The path of the selection `e`, which must start at a variable. */
    def of(e: Expr): VariablePath = HeapAccessor.fromExpression(e) match {
      case (root: Variable, accessors) => VariablePath(root, accessors)
      case _ => throw AliasingRewriteException.unrebuildableValue(e)
    }
  }

  /** Binds to fresh variables the arguments, receivers and indices that the refreshes need to name. */
  def normalizeBody(body: Expr)(using symbols: Symbols): Expr = {
    object normalizer extends ConcreteOOSelfTreeTransformer {
      private val introducedIds = scala.collection.mutable.Set.empty[Identifier]

      override def transform(e: Expr): Expr = {
        def needsArgumentBindings(call: Expr): Boolean = {
          val Operator(args, _) = call: @unchecked

          args.exists(arg => symbols.isMutableType(arg.getType) || exprOps.hasEffect(arg))
        }

        def bindArgument(argument: Expr): (Seq[(ValDef, Expr)], Expr) = {
          if (symbols.isMutableType(argument.getType)) {
            return (Seq.empty, transform(argument))
          }

          bindUnlessImmutable(argument, "argument")
        }

        e match {
          case Let(vd, value @ (_: FunctionInvocation | _: ApplyLetRec | _: Application), rest) if CallResult.isWithin(rest) && changingIndices(value).nonEmpty =>
            val Operator(args, _) = value: @unchecked

            if (args.exists(exprOps.hasEffect)) {
              throw AliasingRewriteException.effectfulIndexedCall(value)
            }

            val indexVariables = changingIndices(value).toSeq.map(index => index -> ValDef.fresh("index", index.getType).copiedFrom(index))
            val withIndexVariables = exprOps.postMap(index => indexVariables.collectFirst { case (`index`, variable) => variable.toVariable.copiedFrom(index) })

            val rebindWriteBacks = exprOps.postMap {
              case assignment @ Assignment(v, annotated @ Annotated(written, flags)) if exprOps.variablesOf(written).exists(_.id == vd.id) =>
                val reboundFlags = flags.map(flag => WriteBack.location(flag).fold(flag)(location => WriteBack.flag(withIndexVariables(location))))

                Some(Assignment(v, Annotated(withIndexVariables(written), reboundFlags).copiedFrom(annotated)).copiedFrom(assignment))

              case _ =>
                None
            }

            val indexBindings = indexVariables.map { case (index, variable) => variable -> transform(index) }
            val boundLet = transform(Let(vd, withIndexVariables(value), rebindWriteBacks(rest)).copiedFrom(e))

            withBindings(indexBindings, boundLet)

          case Let(vd, value, rest) =>
            val (bindings, inner) = splitBindings(transform(value))

            withBindings(bindings, Let(vd, inner, transform(rest)).copiedFrom(e))

          case LetVar(vd, value, rest) =>
            val (bindings, inner) = splitBindings(transform(value))

            withBindings(bindings, LetVar(vd, inner, transform(rest)).copiedFrom(e))

          case Assignment(v, value) =>
            val (bindings, inner) = splitBindings(transform(value))

            withBindings(bindings, Assignment(v, inner).copiedFrom(e))

          case Block(exprs, last) =>
            val statements = exprs.map(transform)
            val result = transform(last)

            statements.foldRight(result) { (statement, rest) =>
              val (bindings, inner) = splitBindings(statement)
              val block = rest match {
                case Block(restStatements, restResult) => Block(inner +: restStatements, restResult).copiedFrom(e)
                case _ => Block(Seq(inner), rest).copiedFrom(e)
              }

              withBindings(bindings, block)
            }

          case call @ (_: FunctionInvocation | _: ApplyLetRec) if needsArgumentBindings(call) =>
            val Operator(args, rebuild) = call: @unchecked
            val (bindings, normalizedArgs) = args.map(bindArgument).unzip

            withBindings(bindings.flatten, rebuild(normalizedArgs).copiedFrom(call))

          case FieldAssignment(obj, selector, value) if exprOps.hasEffect(value) =>
            val (receiverBindings, receiver) = bind(obj, "receiver")
            val (valueBindings, assigned) = bind(value, "value")

            withBindings(receiverBindings ++ valueBindings, FieldAssignment(receiver, selector, assigned).copiedFrom(e))

          case FieldAssignment(obj, selector, value) =>
            val (bindings, receiver) = normalizePath(obj)

            withBindings(bindings, FieldAssignment(receiver, selector, transform(value)).copiedFrom(e))

          case ArrayUpdate(array, index, value) =>
            val (bindings, receiver, normalizedIndex) = normalizeUpdate(array, index, "index")

            withBindings(bindings, ArrayUpdate(receiver, normalizedIndex, transform(value)).copiedFrom(e))

          case MutableMapUpdate(map, key, value) =>
            val (bindings, receiver, normalizedKey) = normalizeUpdate(map, key, "key")

            withBindings(bindings, MutableMapUpdate(receiver, normalizedKey, transform(value)).copiedFrom(e))

          case ArraySelect(array, index) =>
            val (bindings, normalizedArray, normalizedIndex) = normalizeAccess(array, index, "array", "index")

            withBindings(bindings, ArraySelect(normalizedArray, normalizedIndex).copiedFrom(e))

          case ArrayUpdated(array, index, value) =>
            val (bindings, normalizedArray, normalizedIndex) = normalizeAccess(array, index, "array", "index")

            withBindings(bindings, ArrayUpdated(normalizedArray, normalizedIndex, transform(value)).copiedFrom(e))

          case MutableMapUpdated(map, key, value) =>
            val (bindings, normalizedMap, normalizedKey) = normalizeAccess(map, key, "map", "key")

            withBindings(bindings, MutableMapUpdated(normalizedMap, normalizedKey, transform(value)).copiedFrom(e))

          case MutableMapApply(map, key) =>
            val (bindings, normalizedMap, normalizedKey) = normalizeAccess(map, key, "map", "key")

            withBindings(bindings, MutableMapApply(normalizedMap, normalizedKey).copiedFrom(e))

          case _: ClassSelector | _: TupleSelect =>
            val exprOps.Deconstructor(owner +: rest, rebuild) = e: @unchecked
            val (bindings, inner) = splitBindings(transform(owner))

            withBindings(bindings, rebuild(inner +: rest).copiedFrom(e))

          case _ =>
            super.transform(e)
        }
      }

      /** The indices and keys read in `e` that may change while `e` runs. */
      private def changingIndices(e: Expr): Set[Expr] = exprOps.collect[Expr] {
        case ArraySelect(_, index) if !symbols.isImmutableExpression(index) => Set(index)
        case MutableMapApply(_, key) if !symbols.isImmutableExpression(key) => Set(key)
        case _ => Set.empty
      }(e)

      /** `body` under the bindings `bindings`, in order. */
      private def withBindings(bindings: Seq[(ValDef, Expr)], body: Expr): Expr =
        bindings.foldRight(body) { case ((vd, value), rest) => Let(vd, value, rest).copiedFrom(value) }

      /** The bindings this normalizer introduced at the head of `e`, and what they bind in. */
      private def splitBindings(e: Expr): (Seq[(ValDef, Expr)], Expr) = e match {
        case Let(vd, value, rest) if introducedIds(vd.id) =>
          val (bindings, inner) = splitBindings(rest)

          ((vd -> value) +: bindings, inner)

        case _ =>
          (Seq.empty, e)
      }

      /** Binds what is not a variable or a selection in the receiver `e`, with its indices. */
      private def normalizePath(e: Expr): (Seq[(ValDef, Expr)], Expr) = e match {
        case v: Variable =>
          (Seq.empty, v)

        case _: ClassSelector | _: TupleSelect | _: AsInstanceOf | _: Annotated =>
          val exprOps.Deconstructor(owner +: rest, rebuild) = e: @unchecked
          val (bindings, normalizedOwner) = normalizePath(owner)

          (bindings, rebuild(normalizedOwner +: rest).copiedFrom(e))

        case ArraySelect(owner, index) =>
          val (ownerBindings, normalizedOwner) = normalizePath(owner)
          val (indexBindings, normalizedIndex) = bindUnlessImmutable(index, "index")

          (ownerBindings ++ indexBindings, ArraySelect(normalizedOwner, normalizedIndex).copiedFrom(e))

        case MutableMapApply(owner, key) =>
          val (ownerBindings, normalizedOwner) = normalizePath(owner)
          val (keyBindings, normalizedKey) = bindUnlessImmutable(key, "key")

          (ownerBindings ++ keyBindings, MutableMapApply(normalizedOwner, normalizedKey).copiedFrom(e))

        case _ =>
          bind(e, "receiver")
      }

      /** Binds the receiver and the index of an update. */
      private def normalizeUpdate(collection: Expr, index: Expr, indexName: String): (Seq[(ValDef, Expr)], Expr, Expr) = {
        val (collectionBindings, receiver) = normalizePath(collection)
        val (indexBindings, normalizedIndex) = bindUnlessImmutable(index, indexName)

        (collectionBindings ++ indexBindings, receiver, normalizedIndex)
      }

      /** Binds the index of an access, and the collection too when the index is bound. */
      private def normalizeAccess(collection: Expr, index: Expr, collectionName: String, indexName: String): (Seq[(ValDef, Expr)], Expr, Expr) = {
        def bindCollection: (Seq[(ValDef, Expr)], Expr) = {
          if (symbols.isImmutableExpression(index)) {
            return (Seq.empty, transform(collection))
          }

          bindUnlessImmutable(collection, collectionName)
        }

        val (collectionBindings, normalizedCollection) = bindCollection
        val (indexBindings, normalizedIndex) = bindUnlessImmutable(index, indexName)

        (collectionBindings ++ indexBindings, normalizedCollection, normalizedIndex)
      }

      /** Binds `e` to a fresh variable named after `name`, unless it is immutable. */
      private def bindUnlessImmutable(e: Expr, name: String): (Seq[(ValDef, Expr)], Expr) = {
        if (symbols.isImmutableExpression(e)) {
          return (Seq.empty, e)
        }

        bind(e, name)
      }

      /** Binds `e` to a fresh variable named after `name`. */
      private def bind(e: Expr, name: String): (Seq[(ValDef, Expr)], Expr) = {
        val vd = ValDef.fresh(name, e.getType).copiedFrom(e)
        introducedIds += vd.id

        (Seq(vd -> transform(e)), vd.toVariable)
      }
    }

    normalizer.transform(body)
  }

  /** The refreshes to run after each mutation, write back and call of `analysis`, keyed by the expression they follow. */
  def resolveRefreshes(analysis: HeapApproximationAnalysis)(using symbols: Symbols): Map[ExpressionID, Seq[Refresh]] = {
    def resolveDeclarations(functionAnalysis: HeapApproximationAnalysis): Map[Identifier, ValDef] = {
      val params = functionAnalysis.graph.params.map(vd => vd.id -> vd).toMap
      val locals = functionAnalysis.graph.points.values
        .collect {
          case ProgramPoint(_, Let(vd, _, _), _) => vd.id -> vd
          case ProgramPoint(_, LetVar(vd, _, _), _) => vd.id -> vd
        }
        .toMap

      params ++ locals
    }

    def resolvePendingResults(functionAnalysis: HeapApproximationAnalysis): Set[Identifier] =
      functionAnalysis.graph.points.values
        .flatMap(_.e match {
          case e @ WriteBack(_) =>
            exprOps.collect[Identifier] {
              case result @ CallResult() => exprOps.variablesOf(result).map(_.id)
              case _ => Set.empty
            }(e.value)

          case _ =>
            Set.empty[Identifier]
        })
        .toSet

    def resolveResultCalls(functionAnalysis: HeapApproximationAnalysis): Map[Identifier, ProgramPoint] =
      functionAnalysis.graph.points.values
        .collect {
          case ProgramPoint(_, Let(vd, call @ (_: FunctionInvocation | _: ApplyLetRec | _: Application), _), _) =>
            vd.id -> functionAnalysis.graph.points(ExpressionID(call))
        }
        .toMap

    def functionRefreshes(functionAnalysis: HeapApproximationAnalysis, capturedMutations: Map[Identifier, Set[Identifier]]): Seq[(ExpressionID, Seq[Refresh])] = {
      val declarations = resolveDeclarations(functionAnalysis)
      val pendingResults = resolvePendingResults(functionAnalysis)
      val resultCalls = resolveResultCalls(functionAnalysis)

      def resolveVariable(tree: Expr, identifier: Identifier): Variable =
        declarations.get(identifier)
          .map(_.toVariable)
          .getOrElse(throw AliasingRewriteException.unknownVariable(tree))

      def elementRefreshes(tree: Expr, heap: HeapPointApproximation, targets: HeapTargetSet): Seq[Refresh] = {
        val mutated = targets.values
        val traversed = mutated ++ heap.resolveDependencies(targets).flatMap(_.values)
        val collections: Set[HeapValue] = (traversed -- mutated).collect { case collection: HeapCollection => collection }
        val reachable = HeapTargetSet.from(collections.flatMap(heap.resolveAllTargets(_).targets))
        val bound = reachable.filter(target => !traversed(target.value))

        bound.targets.toSeq.flatMap { target =>
          val dependencies = heap.resolveDependencies(HeapTargetSet(Set(target))).toSeq.filterNot(dependency => pendingResults(dependency.variable))
          val source = dependencies.find(_.values.exists(collections))
          val aliases = dependencies.filterNot { dependency =>
            source.exists(sourcePath => sourcePath == dependency || (sourcePath.accessors == dependency.accessors && sourcePath.targets.head == dependency.targets.head))
          }

          if (aliases.nonEmpty && (source.isEmpty || !aliases.forall(_.isDisjoint))) {
            throw AliasingRewriteException.ambiguousAlias(tree)
          }

          aliases.map { other =>
            val holder = resolveVariable(tree, other.variable)
            val value = HeapAccessor.toExpression(resolveVariable(tree, source.get.variable), source.get.accessors)

            Refresh(holder, HeapAccessor.updated(holder, other.accessors, value), HeapTargetCondition.toExpression(other.condition, tree))
          }
        }
      }

      def aliasRefreshes(tree: Expr, heap: HeapPointApproximation, receiver: Expr, ownPath: VariablePath, targets: HeapTargetSet, excluded: Set[Identifier]): Seq[Refresh] = {
        def isCyclic(accessors: Seq[HeapAccessor]): Boolean = targets.targets.exists { target =>
          accessors.exists(_.isInstanceOf[ElementAccessor]) || heap.resolveTargets(target.value, accessors).values.contains(target.value)
        }

        def isInfeasible(dependency: HeapTargetDependency): Boolean = {
          val (shorter, longer) = if (dependency.accessors.size < ownPath.accessors.size) (dependency.accessors, ownPath.accessors) else (ownPath.accessors, dependency.accessors)

          dependency.variable == ownPath.root.id && shorter.size < longer.size && longer.startsWith(shorter) && !isCyclic(longer.drop(shorter.size))
        }

        val aliases = heap.resolveDependencies(targets).toSeq
          .filterNot(ownPath.isPathOf)
          .filterNot(dependency => excluded(dependency.variable))
          .filterNot(isInfeasible)

        if (aliases.nonEmpty && (!targets.isDisjoint || !aliases.forall(_.isDisjoint))) {
          throw AliasingRewriteException.ambiguousAlias(tree)
        }

        val conditionsByPath = aliases.groupMapReduce(dependency => (dependency.variable, dependency.accessors))(_.condition)(_ ++ _)
        val refreshes = conditionsByPath.toSeq.map { case ((identifier, accessors), conditions) =>
          val holder = resolveVariable(tree, identifier)

          Refresh(holder, HeapAccessor.updated(holder, accessors, receiver), HeapTargetCondition.toExpression(conditions, tree))
        }

        refreshes ++ elementRefreshes(tree, heap, targets)
      }

      def mutationRefreshes(tree: Expr, heap: HeapPointApproximation, receiver: Expr, accessor: HeapAccessor, value: Expr): Seq[Refresh] = {
        val targets = heap.resolveTargets(functionAnalysis.resolveLocation(heap, receiver))
        val path = VariablePath.of(receiver)
        val ownRefresh = Refresh(path.root, HeapAccessor.updated(path.root, path.accessors :+ accessor, value), BooleanLiteral(true).copiedFrom(tree))

        ownRefresh +: aliasRefreshes(tree, heap, receiver, path, targets, Set.empty)
      }

      def innerRefreshes(tree: Expr, heap: HeapPointApproximation, before: Option[HeapPointApproximation], path: VariablePath, excluded: Set[Identifier]): Seq[Refresh] = {
        def resolveInnerHolders(heap: HeapPointApproximation): Seq[HeapTargetDependency] = {
          val roots = heap.resolveTargets(HeapVariable(path.root.id), path.accessors)
          val inner = roots.flatMap(heap.resolveAllTargets(_)).filter(reached => !roots.values(reached.value))
          val rootDependencies = heap.resolveDependencies(roots)

          heap.resolveDependencies(inner).toSeq
            .filterNot(path.isPrefixOf)
            .filterNot(dependency => excluded(dependency.variable))
            .filterNot(dependency => rootDependencies.exists(_.isPrefixOf(dependency)))
        }

        def isUnchanged(previous: HeapPointApproximation, value: HeapValue): Boolean = {
          val reached = previous.resolveAllTargets(value).values ++ heap.resolveAllTargets(value).values

          reached.forall { target =>
            val slots = previous.resolveSlots(target) ++ heap.resolveSlots(target)
            val holders = if (previous.isAlive(target)) slots :+ target else slots

            holders.forall(holder => previous.references.get(holder) == heap.references.get(holder))
          }
        }

        val holders = before.fold(resolveInnerHolders(heap))(resolveInnerHolders)

        if (holders.isEmpty) {
          return Seq.empty
        }

        val previous = before.getOrElse(throw AliasingRewriteException.innerAlias(tree))

        holders.flatMap { holder =>
          val held = holder.targets.last.restrict(holder.condition).values

          if (held.size != 1) {
            throw AliasingRewriteException.innerAlias(tree)
          }

          heap.resolveDependencies(HeapTargetSet.of(held.head)).find(path.isPrefixOf) match {
            case Some(source) =>
              val variable = resolveVariable(tree, holder.variable)
              val value = HeapAccessor.toExpression(path.root, source.accessors)

              Seq(Refresh(variable, HeapAccessor.updated(variable, holder.accessors, value), HeapTargetCondition.toExpression(holder.condition, tree)))

            case None if isUnchanged(previous, held.head) =>
              Seq.empty

            case None =>
              throw AliasingRewriteException.innerAlias(tree)
          }
        }
      }

      def pathRefreshes(tree: Expr, heap: HeapPointApproximation, before: Option[HeapPointApproximation], path: VariablePath, excluded: Set[Identifier]): Seq[Refresh] = {
        val targets = heap.resolveTargets(HeapVariable(path.root.id), path.accessors)
        val receiver = HeapAccessor.toExpression(path.root, path.accessors)

        aliasRefreshes(tree, heap, receiver, path, targets, excluded).filterNot(refresh => excluded(refresh.holder.id)) ++
          innerRefreshes(tree, heap, before, path, excluded)
      }

      def resolveCallHeap(call: ProgramPoint): Option[HeapPointApproximation] =
        Option.when(functionAnalysis.isEntered(call.e))(functionAnalysis.resolveParentHeap(call))

      def writeBackRefreshes(tree: Assignment, heap: HeapPointApproximation, target: Expr): Seq[Refresh] = {
        val valueVariables = exprOps.variablesOf(tree.value).map(_.id)
        val before = valueVariables.flatMap(resultCalls.get).headOption.flatMap(resolveCallHeap)
        val ownRefresh = Refresh(tree.v, tree.value, BooleanLiteral(true).copiedFrom(tree))

        ownRefresh +: pathRefreshes(tree, heap, before, VariablePath.of(target), valueVariables)
      }

      def captureRefreshes(tree: ApplyLetRec, heap: HeapPointApproximation): Seq[Refresh] = {
        val captures = functionAnalysis.resolveLocalFunction(tree.id).toSeq
          .flatMap(_.capturedVariables)
          .filter(vd => capturedMutations(tree.id)(vd.id))

        val before = resolveCallHeap(functionAnalysis.graph.points(ExpressionID(tree)))

        captures.flatMap(vd => pathRefreshes(tree, heap, before, VariablePath(vd.toVariable, Seq.empty), Set.empty))
      }

      def refreshesAt(point: ProgramPoint): Option[Seq[Refresh]] = (point.e, functionAnalysis.heapAt.get(point.id)) match {
        case (_: FieldAssignment | _: ArrayUpdate | _: MutableMapUpdate | WriteBack(_), None) => Some(Seq.empty)
        case (e @ FieldAssignment(obj, selector, value), Some(heap)) => Some(mutationRefreshes(e, heap, obj, FieldAccessor(selector), value))
        case (e @ ArrayUpdate(array, index, value), Some(heap)) => Some(mutationRefreshes(e, heap, array, ElementAccessor(index), value))
        case (e @ MutableMapUpdate(map, key, value), Some(heap)) => Some(mutationRefreshes(e, heap, map, ElementAccessor(key), value))
        case (e @ WriteBack(target), Some(heap)) => Some(writeBackRefreshes(e, heap, target))
        case (e: ApplyLetRec, Some(heap)) if capturedMutations(e.id).nonEmpty => Some(captureRefreshes(e, heap))
        case _ => None
      }

      functionAnalysis.graph.points.values.toSeq.flatMap(point => refreshesAt(point).map(point.id -> _))
    }

    val capturedMutations: Map[Identifier, Set[Identifier]] = analysis.functionAnalyses
      .collect { case function: LocalFunctionAnalysis => function.definition.fd.id -> function.resolveCapturedMutations }
      .toMap
      .withDefaultValue(Set.empty)

    analysis.analyses
      .flatMap { functionAnalysis =>
        functionRefreshes(functionAnalysis, capturedMutations)
      }
      .toMap
  }

  /** The assertions that the indices of each update and call of `analysis` differ from those of the slots other variables hold. */
  def resolveDistinctIndices(analysis: HeapApproximationAnalysis)(using symbols: Symbols): Map[ExpressionID, Seq[Expr]] = {
    def assertionsOf(functionAnalysis: HeapApproximationAnalysis): Seq[(ExpressionID, Seq[Expr])] = {
      def distinctAssertions(tree: Expr, indices: Iterable[(Expr, Expr)]): Seq[Expr] =
        indices.toSeq.distinct.map { case (first, second) => Not(Equals(first, second).copiedFrom(tree)).copiedFrom(tree) }

      def updateAssertions(tree: Expr, heap: HeapPointApproximation, collection: Expr, index: Expr): Seq[Expr] = {
        def isBound(slot: HeapElement): Boolean =
          heap.resolveDependencies(heap.resolveAllTargets(slot))
            .exists(dependency => !dependency.isReachable(slot.owner))

        val location = functionAnalysis.resolveLocation(heap, collection)
        val boundIndices = heap.resolveValues[HeapCollection](location)
          .flatMap(heap.resolveSlots)
          .collect { case slot: HeapElement if isBound(slot) => slot.index }
        val otherIndices = boundIndices.filterNot(_ == index)

        distinctAssertions(tree, otherIndices.map(index -> _))
      }

      def argumentAssertions(tree: Expr, heap: HeapPointApproximation, args: Seq[Expr]): Seq[Expr] = {
        def firstDifference(first: Seq[HeapAccessor], second: Seq[HeapAccessor]): Option[(Expr, Expr)] =
          first
            .zip(second)
            .dropWhile { case (left, right) => left == right }
            .headOption
            .collect { case (ElementAccessor(left), ElementAccessor(right)) => left -> right }

        val mutableArgs = args.filter(arg => symbols.isMutableType(arg.getType))
        val dependencies = mutableArgs.map { arg =>
          val location = functionAnalysis.resolveLocation(heap, arg)

          heap.resolveDependencies(heap.resolveAllTargets(location)).toSeq
        }

        val differences = for {
          i <- dependencies.indices
          j <- dependencies.indices
          if i < j
          first <- dependencies(i)
          second <- dependencies(j)
          if first.variable == second.variable
          indices <- firstDifference(first.accessors, second.accessors)
        } yield indices

        distinctAssertions(tree, differences)
      }

      def assertionsAt(point: ProgramPoint): Option[Seq[Expr]] = (point.e, functionAnalysis.heapAt.get(point.id)) match {
        case (e: ArrayUpdate, Some(heap)) => Some(updateAssertions(e, heap, e.array, e.index))
        case (e: MutableMapUpdate, Some(heap)) => Some(updateAssertions(e, heap, e.map, e.key))
        case (e: ArrayUpdated, Some(heap)) if !CallResult.isWithin(e.value) => Some(updateAssertions(e, heap, e.array, e.index))
        case (e: MutableMapUpdated, Some(heap)) if !CallResult.isWithin(e.value) => Some(updateAssertions(e, heap, e.map, e.key))
        case (e: FunctionInvocation, Some(heap)) => Some(argumentAssertions(e, heap, e.args))
        case (e: ApplyLetRec, Some(heap)) => Some(argumentAssertions(e, heap, e.args))
        case (e: Application, Some(heap)) => Some(argumentAssertions(e, heap, e.args))
        case _ => None
      }

      functionAnalysis.graph.points.values.toSeq.flatMap(point => assertionsAt(point).map(point.id -> _))
    }

    analysis.analyses.flatMap(assertionsOf).toMap
  }

  /** Rejects a lambda, other than a postcondition, that captures a variable assigned in `body` or promoted to a `var`. */
  def ensureLambdaCaptures(body: Expr, promotions: Set[Identifier]): Unit = {
    val assigned = exprOps.collect[Identifier] {
      case Assignment(v, _) => Set(v.id)
      case _ => Set.empty
    }(body)

    val postconditions = exprOps.collect[ExpressionID] {
      case Ensuring(_, postcondition) => Set(ExpressionID(postcondition))
      case _ => Set.empty
    }(body)

    exprOps.preTraversal {
      case lambda @ Lambda(params, lambdaBody) if !postconditions(ExpressionID(lambda)) =>
        val captured = exprOps.variablesOf(lambdaBody).map(_.id) -- params.map(_.id)

        if (captured.exists(id => promotions(id) || assigned(id))) {
          throw AliasingRewriteException.staleCapture(lambda)
        }

      case _ =>
    }(body)
  }

  /** The variables in scope at each expression of `body`. */
  def resolveScopes(body: Expr): Map[ExpressionID, Set[Identifier]] = {
    def visit(e: Expr, bound: Set[Identifier]): Map[ExpressionID, Set[Identifier]] = {
      val children: Seq[(Expr, Set[Identifier])] = e match {
        case Let(vd, value, rest) => Seq(value -> bound, rest -> (bound + vd.id))
        case LetVar(vd, value, rest) => Seq(value -> bound, rest -> (bound + vd.id))
        case Lambda(params, lambdaBody) => Seq(lambdaBody -> (bound ++ params.map(_.id)))
        case _ =>
          val exprOps.Deconstructor(subExpressions, _) = e: @unchecked

          subExpressions.map(_ -> bound)
      }

      children.foldLeft(Map(ExpressionID(e) -> bound)) { case (boundAt, (child, childBound)) =>
        boundAt ++ visit(child, childBound)
      }
    }

    visit(body, Set.empty)
  }

  /** `body` with the refreshes and assertions inserted, and the refreshed variables promoted to `var`s. */
  def rewriteBody(
    body: Expr,
    refreshes: Map[ExpressionID, Seq[Refresh]],
    distinctIndices: Map[ExpressionID, Seq[Expr]],
    scopes: Map[ExpressionID, Set[Identifier]],
    promotions: Set[Identifier]
  )(using Symbols): Expr = {
    object transformer extends ConcreteOOSelfTreeTransformer {
      private val declaredIds = scopes.values.flatten.toSet

      override def transform(e: Expr): Expr =
        distinctIndices
          .getOrElse(ExpressionID(e), Seq.empty)
          .foldRight(rewritten(e))(withAssertion(e, _, _))

      /** `e` followed by its refreshes, or with its variables promoted. */
      private def rewritten(e: Expr): Expr = {
        val id = ExpressionID(e)

        if (refreshes.contains(id)) {
          val statements = refreshes(id).map(refreshStatement(e, _))

          return e match {
            case call: ApplyLetRec =>
              val result = ValDef.fresh("result", call.getType).copiedFrom(call)

              Let(result, super.transform(call), transform(Block(statements, result.toVariable).copiedFrom(call))).copiedFrom(call)

            case _ =>
              super.transform(Block(statements, UnitLiteral().copiedFrom(e)).copiedFrom(e))
          }
        }

        e match {
          case Let(vd, value, body) if promotions(vd.id) =>
            LetVar(vd.toVar, transform(value), transform(body)).copiedFrom(e)

          case LetVar(vd, value, body) if promotions(vd.id) && !vd.flags.contains(IsVar) =>
            LetVar(vd.toVar, transform(value), transform(body)).copiedFrom(e)

          case v: Variable if promotions(v.id) =>
            Variable(v.id, v.tpe, (v.flags :+ IsVar).distinct).copiedFrom(v)

          case Annotated(inner, flags) if flags.exists(WriteBack.location(_).isDefined) =>
            Annotated(transform(inner), flags.filter(WriteBack.location(_).isEmpty)).copiedFrom(e)

          case _ =>
            super.transform(e)
        }
      }

      /** The assignment of `refresh`, guarded by its condition. */
      private def refreshStatement(tree: Expr, refresh: Refresh): Expr = {
        if (isOutOfScope(tree, refresh.condition)) {
          throw AliasingRewriteException.conditionOutOfScope(tree)
        }

        if (isOutOfScope(tree, refresh.value)) {
          throw AliasingRewriteException.keyOutOfScope(tree)
        }

        val assignment = Assignment(refresh.holder, refresh.value).copiedFrom(tree)

        if (refresh.condition == BooleanLiteral(true)) {
          return assignment
        }

        val guard = Annotated(refresh.condition, Seq(DropVCs)).copiedFrom(tree)

        IfExpr(guard, assignment, UnitLiteral().copiedFrom(tree)).copiedFrom(tree)
      }

      /** `rest`, after asserting `condition`. */
      private def withAssertion(tree: Expr, condition: Expr, rest: Expr): Expr = {
        if (isOutOfScope(tree, condition)) {
          throw AliasingRewriteException.keyOutOfScope(tree)
        }

        Assert(condition, Some("distinct collection indices"), rest).copiedFrom(tree)
      }

      /** Whether `e` mentions a variable of the body that is not in scope at `tree`. */
      private def isOutOfScope(tree: Expr, e: Expr): Boolean = {
        val scope = scopes.getOrElse(ExpressionID(tree), Set.empty)

        exprOps.variablesOf(e).exists(variable => declaredIds(variable.id) && !scope(variable.id))
      }
    }

    transformer.transform(body)
  }
}

/** Rewrites the mutations of aliased objects into assignments that refresh every variable holding them, from a heap approximation of each function. */
class AssignmentRewrite(override val s: Trees)(override val t: s.type)(using override val context: inox.Context)
  extends oo.SimplePhase
     with IdentitySorts
     with oo.SimplyCachedClasses
     with oo.SimplyCachedTypeDefs
     with AssignmentRewrites { self =>
  import s._

  override protected final val funCache = new ExtractionCache[s.FunDef, (FunctionResult, FunctionSummary)]((fd, context) =>
    getDependencyKey(fd.id)(using context.symbols)
  )

  /** Rewrites the functions of `symbols`, normalized first. */
  protected class TransformerContext(override val s: self.s.type, override val t: s.type)
                                    (using val symbols: s.Symbols)
    extends oo.ConcreteTreeTransformer(s, t) {

    /** The symbols with every function normalized. */
    lazy val preprocessed: s.Symbols = symbols.withFunctions(symbols.functions.values.toSeq.map(preprocess))

    override def transform(fd: s.FunDef): t.FunDef = {
      given s.Symbols = preprocessed

      def rewrite(body: Expr, analysis: HeapApproximationAnalysis): Expr = {
        val refreshes = resolveRefreshes(analysis)
        val distinctIndices = resolveDistinctIndices(analysis)
        val promotions = refreshes.values.flatten.map(_.holder.id).toSet
        ensureLambdaCaptures(body, promotions)

        val scopes = resolveScopes(body)

        rewriteBody(body, refreshes, distinctIndices, scopes, promotions)
      }

      def rewriteSpecification(spec: exprOps.Specification): exprOps.Specification = spec match {
        case exprOps.Postcondition(lambda @ Lambda(params, post)) if exprOps.containsEffect(post) =>
          val analysis = HeapApproximationAnalysis.refineSpecification(lambda)

          exprOps.Postcondition(Lambda(params, rewrite(post, analysis)).copiedFrom(lambda))

        case exprOps.Precondition(pre) if exprOps.containsEffect(pre) =>
          val analysis = HeapApproximationAnalysis.refineSpecification(Lambda(Seq.empty, pre).copiedFrom(pre))

          exprOps.Precondition(rewrite(pre, analysis))

        case _ =>
          spec
      }

      val preprocessedFd = preprocessed.getFunction(fd.id)
      val (specs, bodyOpt) = exprOps.deconstructSpecs(preprocessedFd.fullBody)

      if (bodyOpt.isEmpty) {
        return super.transform(fd)
      }

      val body = bodyOpt.get
      val analysis = HeapApproximationAnalysis.refineDefinition(preprocessedFd.typed)

      val transformedBody = rewrite(body, analysis)
      val transformedSpecs = specs.map(rewriteSpecification)
      val transformedFullBody = exprOps.reconstructSpecs(transformedSpecs, Some(transformedBody), fd.returnType)

      super.transform(fd.copy(fullBody = transformedFullBody).copiedFrom(fd))
    }

    /** `fd` with fresh expression instances and a normalized body and specifications. */
    private def preprocess(fd: FunDef): FunDef = {
      def freshenInstances(body: Expr): Expr =
        exprOps.postMap {
          case v: Variable => Some(Variable(v.id, v.tpe, v.flags).copiedFrom(v))
          case e =>
            val exprOps.Deconstructor(children, builder) = e: @unchecked

            Some(builder(children).copiedFrom(e))
        }(body)

      def normalize(e: Expr): Expr = normalizeBody(freshenInstances(e))

      val (specs, bodyOpt) = exprOps.deconstructSpecs(fd.fullBody)
      val normalizedBody = bodyOpt.map(normalize)
      val normalizedSpecs = specs.map {
        case exprOps.Postcondition(lambda @ Lambda(params, post)) if exprOps.containsEffect(post) =>
          exprOps.Postcondition(Lambda(params, normalize(post)).copiedFrom(lambda))

        case exprOps.Precondition(pre) if exprOps.containsEffect(pre) =>
          exprOps.Precondition(normalize(pre))

        case spec =>
          spec
      }

      fd.copy(fullBody = exprOps.reconstructSpecs(normalizedSpecs, normalizedBody, fd.returnType)).copiedFrom(fd)
    }
  }

  override protected def getContext(syms: s.Symbols) = new TransformerContext(self.s, self.t)(using syms)
}

object AssignmentRewrite {
  /** The phase over the trees `tt`. */
  def apply(tt: Trees)(using inox.Context): ExtractionPipeline {
    val s: tt.type
    val t: tt.type
  } = {
    class Impl(override val s: tt.type, override val t: tt.type) extends AssignmentRewrite(s)(t)

    new Impl(tt, tt)
  }
}
