/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package imperative

trait AssignmentRewrites extends HeapApproximationAnalyses {
  import s._

  case class Refresh(holder: Variable, value: Expr, condition: Expr)

  case class VariablePath(root: Variable, accessors: Seq[HeapAccessor]) {
    def isPathOf(dependency: HeapTargetDependency): Boolean =
      dependency.variable == root.id && dependency.accessors == accessors

    def isPrefixOf(dependency: HeapTargetDependency): Boolean =
      dependency.variable == root.id && dependency.accessors.startsWith(accessors)
  }

  object VariablePath {
    def of(e: Expr): VariablePath = HeapAccessor.fromExpression(e) match {
      case (root: Variable, accessors) => VariablePath(root, accessors)
      case _ => throw AliasingRewriteException.unrebuildableValue(e)
    }
  }

  def normalizeBody(body: Expr)(using symbols: Symbols): Expr = {
    object normalizer extends ConcreteOOSelfTreeTransformer {
      private val introduced = scala.collection.mutable.Set.empty[Identifier]

      override def transform(e: Expr): Expr = {
        def hasEffects(expr: Expr): Boolean = exprOps.exists {
          case _: Assignment | _: FieldAssignment | _: ArrayUpdate | _: MutableMapUpdate => true
          case _ => false
        }(expr)

        def bindArgument(argument: Expr): (Seq[(ValDef, Expr)], Expr) = {
          if (symbols.isMutableType(argument.getType)) {
            return (Seq.empty, transform(argument))
          }

          bindValue(argument, "argument")
        }

        e match {
          case Let(vd, value, rest) if CallResult.isWithin(rest) && callIndices(value).nonEmpty =>
            val Operator(args, _) = value: @unchecked
            if (args.exists(hasEffects)) {
              throw AliasingRewriteException.effectfulIndexedCall(value)
            }

            val indices = callIndices(value).toSeq.map(index => index -> ValDef.fresh("index", index.getType).copiedFrom(index))
            val shared = indices.toMap
            val bound = exprOps.postMap(index => shared.get(index).map(_.toVariable.copiedFrom(index)))

            val writeBacks = exprOps.postMap {
              case assignment @ Assignment(v, annotated @ Annotated(written, flags)) if exprOps.variablesOf(written).exists(_.id == vd.id) =>
                val located = flags.map(flag => WriteBack.location(flag).fold(flag)(location => WriteBack.flag(bound(location))))
                Some(Assignment(v, Annotated(bound(written), located).copiedFrom(annotated)).copiedFrom(assignment))
              case _ => None
            }

            val indexBindings = indices.map { case (index, binding) => binding -> transform(index) }
            val boundLet = transform(Let(vd, bound(value), writeBacks(rest)).copiedFrom(e))
            wrap(indexBindings, boundLet)

          case Let(vd, value, rest) =>
            val (bindings, inner) = floated(transform(value))
            wrap(bindings, Let(vd, inner, transform(rest)).copiedFrom(e))

          case LetVar(vd, value, rest) =>
            val (bindings, inner) = floated(transform(value))
            wrap(bindings, LetVar(vd, inner, transform(rest)).copiedFrom(e))

          case Assignment(v, value) =>
            val (bindings, inner) = floated(transform(value))
            wrap(bindings, Assignment(v, inner).copiedFrom(e))

          case Block(exprs, last) =>
            val statements = exprs.map(transform)
            val result = transform(last)

            statements.foldRight(result) { (statement, rest) =>
              val (bindings, inner) = floated(statement)
              val block = rest match {
                case Block(restStatements, restResult) => Block(inner +: restStatements, restResult).copiedFrom(e)
                case _ => Block(Seq(inner), rest).copiedFrom(e)
              }

              wrap(bindings, block)
            }

          case call @ (_: FunctionInvocation | _: ApplyLetRec) =>
            val Operator(args, rebuild) = call: @unchecked
            val (bindings, normalizedArgs) = args.map(bindArgument).unzip
            wrap(bindings.flatten, rebuild(normalizedArgs).copiedFrom(call))

          case FieldAssignment(obj, selector, value) =>
            val (bindings, receiver) = normalizePath(obj)
            wrap(bindings, FieldAssignment(receiver, selector, transform(value)).copiedFrom(e))

          case ArrayUpdate(array, index, value) =>
            val (bindings, receiver, normalizedIndex) = normalizeWritten(array, index, "index")
            wrap(bindings, ArrayUpdate(receiver, normalizedIndex, transform(value)).copiedFrom(e))

          case MutableMapUpdate(map, key, value) =>
            val (bindings, receiver, normalizedKey) = normalizeWritten(map, key, "key")
            wrap(bindings, MutableMapUpdate(receiver, normalizedKey, transform(value)).copiedFrom(e))

          case ArraySelect(array, index) =>
            val (bindings, normalizedArray, normalizedIndex) = normalizeIndexed(array, index, "array", "index")
            wrap(bindings, ArraySelect(normalizedArray, normalizedIndex).copiedFrom(e))

          case ArrayUpdated(array, index, value) =>
            val (bindings, normalizedArray, normalizedIndex) = normalizeIndexed(array, index, "array", "index")
            wrap(bindings, ArrayUpdated(normalizedArray, normalizedIndex, transform(value)).copiedFrom(e))

          case MutableMapUpdated(map, key, value) =>
            val (bindings, normalizedMap, normalizedKey) = normalizeIndexed(map, key, "map", "key")
            wrap(bindings, MutableMapUpdated(normalizedMap, normalizedKey, transform(value)).copiedFrom(e))

          case MutableMapApply(map, key) =>
            val (bindings, normalizedMap, normalizedKey) = normalizeIndexed(map, key, "map", "key")
            wrap(bindings, MutableMapApply(normalizedMap, normalizedKey).copiedFrom(e))

          case _ =>
            super.transform(e)
        }
      }

      private def callIndices(e: Expr): Set[Expr] = exprOps.collect[Expr] {
        case ArraySelect(_, index) if !symbols.isImmutableExpression(index) => Set(index)
        case MutableMapApply(_, key) if !symbols.isImmutableExpression(key) => Set(key)
        case _ => Set.empty
      }(e)

      private def wrap(bindings: Seq[(ValDef, Expr)], body: Expr): Expr =
        bindings.foldRight(body) { case ((vd, value), rest) => Let(vd, value, rest).copiedFrom(value) }

      private def floated(e: Expr): (Seq[(ValDef, Expr)], Expr) = e match {
        case Let(vd, value, rest) if introduced(vd.id) =>
          val (bindings, inner) = floated(rest)
          ((vd -> value) +: bindings, inner)

        case _ =>
          (Seq.empty, e)
      }

      private def normalizePath(e: Expr): (Seq[(ValDef, Expr)], Expr) = e match {
        case v: Variable =>
          (Seq.empty, v)

        case _: ClassSelector | _: TupleSelect | _: AsInstanceOf | _: Annotated =>
          val exprOps.Deconstructor(owner +: rest, rebuild) = e: @unchecked
          val (bindings, normalizedOwner) = normalizePath(owner)
          (bindings, rebuild(normalizedOwner +: rest).copiedFrom(e))

        case ArraySelect(owner, index) =>
          val (ownerBindings, normalizedOwner) = normalizePath(owner)
          val (indexBindings, normalizedIndex) = bindValue(index, "index")
          (ownerBindings ++ indexBindings, ArraySelect(normalizedOwner, normalizedIndex).copiedFrom(e))

        case MutableMapApply(owner, key) =>
          val (ownerBindings, normalizedOwner) = normalizePath(owner)
          val (keyBindings, normalizedKey) = bindValue(key, "key")
          (ownerBindings ++ keyBindings, MutableMapApply(normalizedOwner, normalizedKey).copiedFrom(e))

        case _ =>
          bind(e, "receiver")
      }

      private def normalizeWritten(collection: Expr, index: Expr, indexName: String): (Seq[(ValDef, Expr)], Expr, Expr) = {
        val (collectionBindings, receiver) = normalizePath(collection)
        val (indexBindings, normalizedIndex) = bindValue(index, indexName)

        (collectionBindings ++ indexBindings, receiver, normalizedIndex)
      }

      private def normalizeIndexed(collection: Expr, index: Expr, collectionName: String, indexName: String): (Seq[(ValDef, Expr)], Expr, Expr) = {
        def bindCollection: (Seq[(ValDef, Expr)], Expr) = {
          if (symbols.isImmutableExpression(index)) {
            return (Seq.empty, transform(collection))
          }

          bindValue(collection, collectionName)
        }

        val (collectionBindings, normalizedCollection) = bindCollection
        val (indexBindings, normalizedIndex) = bindValue(index, indexName)

        (collectionBindings ++ indexBindings, normalizedCollection, normalizedIndex)
      }

      private def bindValue(e: Expr, name: String): (Seq[(ValDef, Expr)], Expr) = {
        if (symbols.isImmutableExpression(e)) {
          return (Seq.empty, e)
        }

        bind(e, name)
      }

      private def bind(e: Expr, name: String): (Seq[(ValDef, Expr)], Expr) = {
        val vd = ValDef.fresh(name, e.getType).copiedFrom(e)
        introduced += vd.id
        (Seq(vd -> transform(e)), vd.toVariable)
      }
    }

    normalizer.transform(body)
  }

  def resolveRefreshes(analysis: HeapApproximationAnalysis)(using symbols: Symbols): Map[ExpressionID, Seq[Refresh]] = {
    def resolveDeclarations(functionAnalysis: HeapApproximationAnalysis): Map[Identifier, ValDef] =
      functionAnalysis.graph.points.values.collect {
        case ProgramPoint(_, Let(vd, _, _), _) => vd.id -> vd
        case ProgramPoint(_, LetVar(vd, _, _), _) => vd.id -> vd
      }.toMap

    def resolvePendingResults(functionAnalysis: HeapApproximationAnalysis): Set[Identifier] =
      functionAnalysis.graph.points.values.flatMap(_.e match {
        case e @ WriteBack(_) =>
          exprOps.collect[Identifier] {
            case result @ CallResult() => exprOps.variablesOf(result).map(_.id)
            case _ => Set.empty
          }(e.value)

        case _ => Set.empty[Identifier]
      }).toSet

    def refreshesOf(
      functionAnalysis: HeapApproximationAnalysis,
      declarations: Map[Identifier, ValDef],
      pendingResults: Set[Identifier]
    ): Seq[(ExpressionID, Seq[Refresh])] = {
      def resolveVariable(tree: Expr, identifier: Identifier): Variable =
        declarations.get(identifier)
          .map(_.toVariable)
          .getOrElse(throw AliasingRewriteException.unknownVariable(tree))

      def boundRefreshes(tree: Expr, heap: HeapPointApproximation, targets: HeapTargetSet): Seq[Refresh] = {
        val mutated = targets.values
        val path = mutated ++ heap.resolveDependencies(targets).flatMap(_.values)
        val collections: Set[HeapValue] = (path -- mutated).collect { case collection: HeapCollection => collection }
        val reachable = HeapTargetSet.from(collections.flatMap(heap.resolveAllTargets(_).targets))
        val bound = reachable.filter(target => !path(target.value))

        bound.targets.toSeq.flatMap { target =>
          val dependencies = heap.resolveDependencies(HeapTargetSet(Set(target))).toSeq.filterNot(dependency => pendingResults(dependency.variable))
          val source = dependencies.find(_.values.exists(collections))
          val others = dependencies.filterNot(dependency => source.exists(sourcePath => sourcePath == dependency || (sourcePath.accessors == dependency.accessors && sourcePath.targets.head == dependency.targets.head)))

          if (others.nonEmpty && (source.isEmpty || !others.forall(_.isDisjoint))) {
            throw AliasingRewriteException.ambiguousAlias(tree)
          }

          others.map { other =>
            val holder = resolveVariable(tree, other.variable)
            val value = HeapAccessor.toExpression(resolveVariable(tree, source.get.variable), source.get.accessors)

            Refresh(holder, HeapAccessor.updated(holder, other.accessors, value), HeapTargetCondition.toExpression(other.condition, tree))
          }
        }
      }

      def foreignRefreshes(tree: Expr, heap: HeapPointApproximation, receiver: Expr, own: VariablePath, targets: HeapTargetSet): Seq[Refresh] = {
        def isCyclic(accessors: Seq[HeapAccessor]): Boolean = targets.targets.exists { target =>
          accessors.exists(_.isInstanceOf[ElementAccessor]) || heap.resolveTargets(target.value, accessors).values.contains(target.value)
        }

        def isInfeasible(dependency: HeapTargetDependency): Boolean = {
          val (shorter, longer) = if (dependency.accessors.size < own.accessors.size) (dependency.accessors, own.accessors) else (own.accessors, dependency.accessors)

          dependency.variable == own.root.id && shorter.size < longer.size && longer.startsWith(shorter) && !isCyclic(longer.drop(shorter.size))
        }

        val foreign = heap.resolveDependencies(targets).toSeq
          .filterNot(own.isPathOf)
          .filterNot(isInfeasible)

        if (foreign.nonEmpty && (!targets.isDisjoint || !foreign.forall(_.isDisjoint))) {
          throw AliasingRewriteException.ambiguousAlias(tree)
        }

        val conditionsByPath = foreign.groupMapReduce(dependency => (dependency.variable, dependency.accessors))(_.condition)(_ ++ _)
        val refreshes = conditionsByPath.toSeq.map { case ((identifier, accessors), conditions) =>
          val holder = resolveVariable(tree, identifier)
          Refresh(holder, HeapAccessor.updated(holder, accessors, receiver), HeapTargetCondition.toExpression(conditions, tree))
        }

        refreshes ++ boundRefreshes(tree, heap, targets)
      }

      def mutationRefreshes(tree: Expr, heap: HeapPointApproximation, receiver: Expr, accessor: HeapAccessor, value: Expr): Seq[Refresh] = {
        val targets = heap.resolveTargets(HeapApproximationAnalysis.resolveLocation(functionAnalysis.graph, heap, receiver))
        val path = VariablePath.of(receiver)
        val ownRefresh = Refresh(path.root, HeapAccessor.updated(path.root, path.accessors :+ accessor, value), BooleanLiteral(true).copiedFrom(tree))

        ownRefresh +: foreignRefreshes(tree, heap, receiver, path, targets)
      }

      def writeBackRefreshes(tree: Assignment, heap: HeapPointApproximation, target: Expr): Seq[Refresh] = {
        val path = VariablePath.of(target)
        val targets = heap.resolveTargets(HeapVariable(path.root.id), path.accessors)
        val values = targets.values
        val inner = targets.flatMap(heap.resolveAllTargets(_)).filter(reached => !values(reached.value))

        val covering = heap.resolveDependencies(targets)
        val innerAliases = heap.resolveDependencies(inner)
          .filterNot(path.isPrefixOf)
          .filterNot(dependency => covering.exists(covered => covered.variable == dependency.variable && dependency.accessors.startsWith(covered.accessors)))

        if (innerAliases.nonEmpty) {
          throw AliasingRewriteException.innerAlias(tree)
        }

        val sources = exprOps.variablesOf(tree.value).map(_.id)
        val refreshes = foreignRefreshes(tree, heap, target, path, targets).filterNot(refresh => sources(refresh.holder.id))
        val ownRefresh = Refresh(tree.v, tree.value, BooleanLiteral(true).copiedFrom(tree))

        ownRefresh +: refreshes
      }

      def refreshesAt(point: ProgramPoint): Option[Seq[Refresh]] = (point.e, functionAnalysis.heapAt.get(point.id)) match {
        case (_: FieldAssignment | _: ArrayUpdate | _: MutableMapUpdate | WriteBack(_), None) => Some(Seq.empty)
        case (e @ FieldAssignment(obj, selector, value), Some(heap)) => Some(mutationRefreshes(e, heap, obj, FieldAccessor(selector), value))
        case (e @ ArrayUpdate(array, index, value), Some(heap)) => Some(mutationRefreshes(e, heap, array, ElementAccessor(index), value))
        case (e @ MutableMapUpdate(map, key, value), Some(heap)) => Some(mutationRefreshes(e, heap, map, ElementAccessor(key), value))
        case (e @ WriteBack(target), Some(heap)) => Some(writeBackRefreshes(e, heap, target))
        case _ => None
      }

      functionAnalysis.graph.points.values.toSeq.flatMap(point => refreshesAt(point).map(point.id -> _))
    }

    analysis.analyses.flatMap { functionAnalysis =>
      refreshesOf(functionAnalysis, resolveDeclarations(functionAnalysis), resolvePendingResults(functionAnalysis))
    }.toMap
  }

  def resolveDistinctIndices(analysis: HeapApproximationAnalysis)(using symbols: Symbols): Map[ExpressionID, Seq[Expr]] = {
    def assertionsOf(functionAnalysis: HeapApproximationAnalysis): Seq[(ExpressionID, Seq[Expr])] = {
      def distinctAssertions(tree: Expr, indices: Iterable[(Expr, Expr)]): Seq[Expr] =
        indices.toSeq.distinct.map { case (first, second) => Not(Equals(first, second).copiedFrom(tree)).copiedFrom(tree) }

      def writtenAssertions(tree: Expr, heap: HeapPointApproximation, collection: Expr, index: Expr): Seq[Expr] = {
        def isBound(slot: HeapElement): Boolean =
          heap.resolveDependencies(heap.resolveAllTargets(slot))
            .exists(dependency => !dependency.isReachable(slot.owner))

        val location = HeapApproximationAnalysis.resolveLocation(functionAnalysis.graph, heap, collection)
        val boundIndices = heap.resolveValues[HeapCollection](location)
          .flatMap(heap.resolveSlots)
          .collect { case slot: HeapElement if isBound(slot) => slot.index }
        val otherIndices = boundIndices.filterNot(_ == index)

        distinctAssertions(tree, otherIndices.map(index -> _))
      }

      def argumentAssertions(tree: Expr, heap: HeapPointApproximation, args: Seq[Expr]): Seq[Expr] = {
        def firstDifference(first: Seq[HeapAccessor], second: Seq[HeapAccessor]): Option[(Expr, Expr)] =
          first.zip(second).dropWhile { case (left, right) => left == right }.headOption.collect {
            case (ElementAccessor(left), ElementAccessor(right)) => left -> right
          }

        val mutableArgs = args.filter(arg => symbols.isMutableType(arg.getType))
        val dependencies = mutableArgs.map { arg =>
          val location = HeapApproximationAnalysis.resolveLocation(functionAnalysis.graph, heap, arg)
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
        case (e: ArrayUpdate, Some(heap)) => Some(writtenAssertions(e, heap, e.array, e.index))
        case (e: MutableMapUpdate, Some(heap)) => Some(writtenAssertions(e, heap, e.map, e.key))
        case (e: ArrayUpdated, Some(heap)) if !CallResult.isWithin(e.value) => Some(writtenAssertions(e, heap, e.array, e.index))
        case (e: MutableMapUpdated, Some(heap)) if !CallResult.isWithin(e.value) => Some(writtenAssertions(e, heap, e.map, e.key))
        case (e: FunctionInvocation, Some(heap)) => Some(argumentAssertions(e, heap, e.args))
        case (e: ApplyLetRec, Some(heap)) => Some(argumentAssertions(e, heap, e.args))
        case (e: Application, Some(heap)) => Some(argumentAssertions(e, heap, e.args))
        case _ => None
      }

      functionAnalysis.graph.points.values.toSeq.flatMap(point => assertionsAt(point).map(point.id -> _))
    }

    analysis.analyses.flatMap(assertionsOf).toMap
  }

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

  def resolveBoundIdentifiers(body: Expr): Map[ExpressionID, Set[Identifier]] = {
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

  def rewriteBody(
    body: Expr,
    refreshes: Map[ExpressionID, Seq[Refresh]],
    distinctIndices: Map[ExpressionID, Seq[Expr]],
    boundIdentifiers: Map[ExpressionID, Set[Identifier]],
    promotions: Set[Identifier]
  )(using Symbols): Expr = {
    object transformer extends ConcreteOOSelfTreeTransformer {
      private val declared = boundIdentifiers.values.flatten.toSet

      override def transform(e: Expr): Expr =
        distinctIndices.getOrElse(ExpressionID(e), Seq.empty).foldRight(rewritten(e))(asserted(e, _, _))

      private def rewritten(e: Expr): Expr = {
        val id = ExpressionID(e)
        if (refreshes.contains(id)) {
          val statements = refreshes(id).map(refreshStatement(e, _))
          return super.transform(Block(statements, UnitLiteral().copiedFrom(e)).copiedFrom(e))
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

      private def asserted(tree: Expr, condition: Expr, rest: Expr): Expr = {
        if (isOutOfScope(tree, condition)) {
          throw AliasingRewriteException.keyOutOfScope(tree)
        }

        Assert(condition, Some("distinct collection indices"), rest).copiedFrom(tree)
      }

      private def isOutOfScope(tree: Expr, e: Expr): Boolean = {
        val bound = boundIdentifiers.getOrElse(ExpressionID(tree), Set.empty)

        exprOps.variablesOf(e).exists(variable => declared(variable.id) && !bound(variable.id))
      }
    }

    transformer.transform(body)
  }
}

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

  protected class TransformerContext(override val s: self.s.type, override val t: s.type)
                                    (using val symbols: s.Symbols)
    extends oo.ConcreteTreeTransformer(s, t) {

    lazy val preprocessed: s.Symbols = symbols.withFunctions(symbols.functions.values.toSeq.map(preprocess))

    override def transform(fd: s.FunDef): t.FunDef = {
      given s.Symbols = preprocessed
      val preprocessedFd = preprocessed.getFunction(fd.id)
      val (specs, bodyOpt) = exprOps.deconstructSpecs(preprocessedFd.fullBody)
      if (bodyOpt.isEmpty) {
        return super.transform(fd)
      }

      val body = bodyOpt.get
      val analysis = HeapApproximationAnalysis.refineDefinition(preprocessedFd.typed)

      val refreshes = resolveRefreshes(analysis)
      val distinctIndices = resolveDistinctIndices(analysis)
      val promotions = refreshes.values.flatten.map(_.holder.id).toSet
      ensureLambdaCaptures(body, promotions)

      val boundIdentifiers = resolveBoundIdentifiers(body)
      val transformedBody = rewriteBody(body, refreshes, distinctIndices, boundIdentifiers, promotions)
      val transformedFullBody = exprOps.reconstructSpecs(specs, Some(transformedBody), fd.returnType)

      super.transform(fd.copy(fullBody = transformedFullBody).copiedFrom(fd))
    }

    private def preprocess(fd: FunDef): FunDef = {
      def freshenInstances(body: Expr): Expr =
        exprOps.postMap {
          case v: Variable => Some(Variable(v.id, v.tpe, v.flags).copiedFrom(v))
          case e =>
            val exprOps.Deconstructor(children, builder) = e: @unchecked
            Some(builder(children).copiedFrom(e))
        }(body)

      val (specs, bodyOpt) = exprOps.deconstructSpecs(fd.fullBody)
      val normalizedBody = bodyOpt.map(body => normalizeBody(freshenInstances(body)))

      fd.copy(fullBody = exprOps.reconstructSpecs(specs, normalizedBody, fd.returnType)).copiedFrom(fd)
    }
  }

  override protected def getContext(syms: s.Symbols) = new TransformerContext(self.s, self.t)(using syms)
}

object AssignmentRewrite {
  def apply(tt: Trees)(using inox.Context): ExtractionPipeline {
    val s: tt.type
    val t: tt.type
  } = {
    class Impl(override val s: tt.type, override val t: tt.type) extends AssignmentRewrite(s)(t)

    new Impl(tt, tt)
  }
}
