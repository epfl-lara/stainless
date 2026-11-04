/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package imperative

trait Transformations extends HeapApproximationAnalyses {
  import s._

  case class Refresh(holder: Variable, value: Expr, condition: Expr)

  def normalizeReceivers(body: Expr)(using symbols: Symbols): Expr = {
    val assigned = exprOps.collect[Identifier] {
      case LetVar(vd, _, _) => Set(vd.id)
      case _ => Set.empty
    }(body)

    val introduced = scala.collection.mutable.Set.empty[Identifier]

    object normalizer extends ConcreteOOSelfTreeTransformer {
      def bindValue(e: Expr, name: String): (Seq[(ValDef, Expr)], Expr) = e match {
        case _ if !needsBinding(e) => (Seq.empty, e)
        case _ =>
          val vd = ValDef.fresh(name, e.getType).copiedFrom(e)
          introduced += vd.id
          (Seq(vd -> transform(e)), vd.toVariable)
      }

      def needsBinding(e: Expr): Boolean = e match {
        case _: Literal[?] => false
        case _ =>
          exprOps.variablesOf(e).exists(variable => assigned(variable.id) || symbols.isMutableType(variable.tpe)) ||
          exprOps.exists { case _: FunctionInvocation | _: Application | _: ApplyLetRec => true; case _ => false }(e)
      }

      def floated(e: Expr): (Seq[(ValDef, Expr)], Expr) = e match {
        case Let(vd, value, rest) if introduced(vd.id) =>
          val (bindings, inner) = floated(rest)
          ((vd -> value) +: bindings, inner)

        case _ =>
          (Seq.empty, e)
      }

      def bindCollection(collection: Expr, index: Expr, name: String): (Seq[(ValDef, Expr)], Expr) =
        if (needsBinding(index)) bindValue(collection, name) else (Seq.empty, transform(collection))

      def normalizePath(e: Expr): (Seq[(ValDef, Expr)], Expr) = e match {
        case v: Variable =>
          (Seq.empty, v)

        case ClassSelector(owner, field) =>
          val (bindings, normalizedOwner) = normalizePath(owner)
          (bindings, ClassSelector(normalizedOwner, field).copiedFrom(e))

        case TupleSelect(owner, index) =>
          val (bindings, normalizedOwner) = normalizePath(owner)
          (bindings, TupleSelect(normalizedOwner, index).copiedFrom(e))

        case AsInstanceOf(owner, tpe) =>
          val (bindings, normalizedOwner) = normalizePath(owner)
          (bindings, AsInstanceOf(normalizedOwner, tpe).copiedFrom(e))

        case Annotated(owner, flags) =>
          val (bindings, normalizedOwner) = normalizePath(owner)
          (bindings, Annotated(normalizedOwner, flags).copiedFrom(e))

        case ArraySelect(owner, index) =>
          val (ownerBindings, normalizedOwner) = normalizePath(owner)
          val (indexBindings, normalizedIndex) = bindValue(index, "index")
          (ownerBindings ++ indexBindings, ArraySelect(normalizedOwner, normalizedIndex).copiedFrom(e))

        case MutableMapApply(owner, key) =>
          val (ownerBindings, normalizedOwner) = normalizePath(owner)
          val (keyBindings, normalizedKey) = bindValue(key, "key")
          (ownerBindings ++ keyBindings, MutableMapApply(normalizedOwner, normalizedKey).copiedFrom(e))

        case _ =>
          bindValue(e, "receiver")
      }

      def wrap(bindings: Seq[(ValDef, Expr)], body: Expr): Expr =
        bindings.foldRight(body) { case ((vd, value), rest) => Let(vd, value, rest).copiedFrom(value) }

      def callIndices(e: Expr): Set[Expr] = exprOps.collect[Expr] {
        case ArraySelect(_, index) if needsBinding(index) => Set(index)
        case MutableMapApply(_, key) if needsBinding(key) => Set(key)
        case _ => Set.empty
      }(e)

      override def transform(e: Expr): Expr = e match {
        case Let(vd, value, rest) if CallResult.isWithin(rest) && callIndices(value).nonEmpty =>
          val indices = callIndices(value).toSeq.map(index => index -> ValDef.fresh("index", index.getType).copiedFrom(index))
          val shared = indices.toMap
          val bound = exprOps.postMap(index => shared.get(index).map(_.toVariable.copiedFrom(index)))

          val writeBacks = exprOps.postMap {
            case assignment @ Assignment(v, annotated @ Annotated(written, flags)) if exprOps.variablesOf(written).exists(_.id == vd.id) =>
              val located = flags.map(flag => WriteBack.location(flag).fold(flag)(location => WriteBack.flag(bound(location))))
              Some(Assignment(v, Annotated(bound(written), located).copiedFrom(annotated)).copiedFrom(assignment))
            case _ => None
          }

          wrap(indices.map { case (index, binding) => binding -> transform(index) }, transform(Let(vd, bound(value), writeBacks(rest)).copiedFrom(e)))

        case Let(vd, value, rest) =>
          val (bindings, inner) = floated(transform(value))
          wrap(bindings, Let(vd, inner, transform(rest)).copiedFrom(e))

        case LetVar(vd, value, rest) =>
          val (bindings, inner) = floated(transform(value))
          wrap(bindings, LetVar(vd, inner, transform(rest)).copiedFrom(e))

        case Assignment(v, value) =>
          val (bindings, inner) = floated(transform(value))
          wrap(bindings, Assignment(v, inner).copiedFrom(e))

        case FieldAssignment(obj, selector, value) =>
          val (bindings, receiver) = normalizePath(obj)
          wrap(bindings, FieldAssignment(receiver, selector, transform(value)).copiedFrom(e))

        case ArrayUpdate(array, index, value) =>
          val (arrayBindings, receiver) = normalizePath(array)
          val (indexBindings, normalizedIndex) = bindValue(index, "index")
          wrap(arrayBindings ++ indexBindings, ArrayUpdate(receiver, normalizedIndex, transform(value)).copiedFrom(e))

        case MutableMapUpdate(map, key, value) =>
          val (mapBindings, receiver) = normalizePath(map)
          val (keyBindings, normalizedKey) = bindValue(key, "key")
          wrap(mapBindings ++ keyBindings, MutableMapUpdate(receiver, normalizedKey, transform(value)).copiedFrom(e))

        case ArraySelect(array, index) =>
          val (arrayBindings, normalizedArray) = bindCollection(array, index, "array")
          val (indexBindings, normalizedIndex) = bindValue(index, "index")
          wrap(arrayBindings ++ indexBindings, ArraySelect(normalizedArray, normalizedIndex).copiedFrom(e))

        case ArrayUpdated(array, index, value) =>
          val (arrayBindings, normalizedArray) = bindCollection(array, index, "array")
          val (indexBindings, normalizedIndex) = bindValue(index, "index")
          wrap(arrayBindings ++ indexBindings, ArrayUpdated(normalizedArray, normalizedIndex, transform(value)).copiedFrom(e))

        case MutableMapUpdated(map, key, value) =>
          val (mapBindings, normalizedMap) = bindCollection(map, key, "map")
          val (keyBindings, normalizedKey) = bindValue(key, "key")
          wrap(mapBindings ++ keyBindings, MutableMapUpdated(normalizedMap, normalizedKey, transform(value)).copiedFrom(e))

        case MutableMapApply(map, key) =>
          val (mapBindings, normalizedMap) = bindCollection(map, key, "map")
          val (keyBindings, normalizedKey) = bindValue(key, "key")
          wrap(mapBindings ++ keyBindings, MutableMapApply(normalizedMap, normalizedKey).copiedFrom(e))

        case _ =>
          super.transform(e)
      }
    }

    normalizer.transform(body)
  }


  def computeRefreshes(analysis: HeapApproximationAnalysis)(using symbols: Symbols): Map[ExpressionID, Seq[Refresh]] = {
    val graph = analysis.graph
    val always = Set(HeapTargetCondition(Seq.empty))

    val declarations: Map[Identifier, ValDef] = graph.points.values.collect {
      case Point(_, Let(vd, _, _), _) => vd.id -> vd
      case Point(_, LetVar(vd, _, _), _) => vd.id -> vd
    }.toMap

    def variable(tree: Expr, identifier: Identifier): Variable =
      declarations.get(identifier)
        .map(_.toVariable)
        .getOrElse(throw AliasingAssignRewriteException.unknownVariable(tree))

    def castTo(value: Expr, tpe: Type): Expr =
      if (symbols.isSubtypeOf(value.getType, tpe)) value
      else Annotated(AsInstanceOf(value, tpe).copiedFrom(value), Seq(DropVCs)).copiedFrom(value)

    def narrow(receiver: Expr, field: Identifier): (Expr, ClassType) = receiver.getType.getType match {
      case receiverType: ClassType =>
        val fieldClass = symbols.classForField(receiverType, field).getOrElse(throw AliasingAssignRewriteException.unknownFieldOwner(receiver))
        val fieldClassType = fieldClass.toType
        val narrowedReceiver =
          if (fieldClassType == receiverType) receiver
          else Annotated(AsInstanceOf(receiver, fieldClassType).copiedFrom(receiver), Seq(DropVCs)).copiedFrom(receiver)

        (narrowedReceiver, fieldClassType)

      case _ =>
        throw AliasingAssignRewriteException.unrebuildableValue(receiver)
    }

    def select(receiver: Expr, field: Identifier): Expr =
      ClassSelector(narrow(receiver, field)._1, field).copiedFrom(receiver)

    def rebuildClass(receiver: Expr, field: Identifier, value: Expr): Expr = {
      val (narrowedReceiver, fieldClassType) = narrow(receiver, field)
      val rebuiltReceiver = ClassConstructor(fieldClassType, fieldClassType.tcd.fields.map { vd =>
        if (vd.id == field) castTo(value, vd.tpe)
        else ClassSelector(narrowedReceiver, vd.id).copiedFrom(receiver)
      }).copiedFrom(value)

      castTo(rebuiltReceiver, receiver.getType)
    }

    def rebuildTuple(receiver: Expr, index: Int, value: Expr): Expr = receiver.getType.getType match {
      case TupleType(bases) =>
        Tuple(bases.indices.map { position =>
          if (position + 1 == index) castTo(value, bases(position))
          else TupleSelect(receiver, position + 1).copiedFrom(receiver)
        }).copiedFrom(value)

      case _ =>
        throw AliasingAssignRewriteException.unrebuildableValue(receiver)
    }

    def rebuild(base: Expr, accessors: Seq[HeapAccessor], value: Expr): Expr = accessors match {
      case Seq() => castTo(value, base.getType)
      case FieldAccessor(field) +: rest => rebuildClass(base, field, rebuild(select(base, field), rest, value))
      case TupleAccessor(index) +: rest => rebuildTuple(base, index, rebuild(TupleSelect(base, index).copiedFrom(base), rest, value))
      case ElementAccessor(index) +: rest => base.getType.getType match {
        case _: ArrayType => ArrayUpdated(base, index, rebuild(ArraySelect(base, index).copiedFrom(base), rest, value)).copiedFrom(base)
        case _: MutableMapType => MutableMapUpdated(base, index, rebuild(MutableMapApply(base, index).copiedFrom(base), rest, value)).copiedFrom(base)
        case _ => throw AliasingAssignRewriteException.unrebuildableValue(base)
      }
    }

    def pathOf(receiver: Expr): Option[(Variable, Seq[HeapAccessor])] = HeapAccessor.fromExpression(receiver) match {
      case (root: Variable, accessors) => Some(root -> accessors)
      case _ => None
    }

    def updated(receiver: Expr, value: Expr): Option[(Variable, Expr)] = receiver match {
      case v: Variable => Some(v -> castTo(value, v.tpe))
      case ClassSelector(owner, field) => updated(owner, rebuildClass(owner, field, value))
      case TupleSelect(owner, index) => updated(owner, rebuildTuple(owner, index, value))
      case ArraySelect(owner, index) => updated(owner, ArrayUpdated(owner, index, value).copiedFrom(receiver))
      case MutableMapApply(owner, key) => updated(owner, MutableMapUpdated(owner, key, value).copiedFrom(receiver))
      case AsInstanceOf(owner, _) => updated(owner, value)
      case Annotated(owner, _) => updated(owner, value)
      case _ => None
    }

    def condition(tree: Expr, conditions: Set[HeapTargetCondition]): Expr = {
      if (conditions.exists(_.choices.isEmpty)) {
        return BooleanLiteral(true).copiedFrom(tree)
      }

      orJoin(conditions.toSeq.map(condition => andJoin(condition.choices.map { case (choice, holds) =>
        if (holds) choice else Not(choice).copiedFrom(tree)
      })))
    }

    def conjoin(conditions: Set[HeapTargetCondition], targets: HeapTargetSet): Set[HeapTarget] =
      targets.targets.map(target => target.withConditions(HeapTargetCondition.and(conditions, target.conditions))).filter(_.conditions.nonEmpty)

    def pathTargets(heap: HeapPointApproximation, path: Expr): HeapTargetSet = path match {
      case v: Variable => heap.resolveTargets(HeapVariable(v.id))
      case ClassSelector(owner, field) => HeapTargetSet.from(pathTargets(heap, owner).targets.flatMap(target => conjoin(target.conditions, heap.resolveTargets(HeapInstanceField(target.instance, field)))))
      case TupleSelect(owner, index) => HeapTargetSet.from(pathTargets(heap, owner).targets.flatMap(target => conjoin(target.conditions, heap.resolveTargets(HeapTupleField(target.instance, index)))))
      case ArraySelect(owner, index) => HeapTargetSet.from(pathTargets(heap, owner).targets.flatMap(target => conjoin(target.conditions, heap.resolveTargets(HeapElement(HeapElements(target.instance), index)))))
      case MutableMapApply(owner, key) => HeapTargetSet.from(pathTargets(heap, owner).targets.flatMap(target => conjoin(target.conditions, heap.resolveTargets(HeapElement(HeapElements(target.instance), key)))))
      case AsInstanceOf(owner, _) => pathTargets(heap, owner)
      case Annotated(owner, _) => pathTargets(heap, owner)
      case _ => throw AliasingAssignRewriteException.unrebuildableValue(path)
    }

    def read(base: Expr, accessors: Seq[HeapAccessor]): Expr = accessors.foldLeft(base) {
      case (owner, FieldAccessor(field)) => select(owner, field)
      case (owner, TupleAccessor(index)) => TupleSelect(owner, index).copiedFrom(owner)
      case (owner, ElementAccessor(index)) => owner.getType.getType match {
        case _: ArrayType => ArraySelect(owner, index).copiedFrom(owner)
        case _: MutableMapType => MutableMapApply(owner, index).copiedFrom(owner)
        case _ => throw AliasingAssignRewriteException.unrebuildableValue(owner)
      }
    }

    val pendingResults: Set[Identifier] = graph.points.values.flatMap(_.e match {
      case e @ WriteBack(_) =>
        exprOps.collect[Identifier] {
          case result @ CallResult() => exprOps.variablesOf(result).map(_.id)
          case _ => Set.empty
        }(e.value)

      case _ => Set.empty[Identifier]
    }).toSet

    def boundRefreshes(tree: Expr, heap: HeapPointApproximation, targets: HeapTargetSet): Seq[Refresh] = {
      val mutated = targets.targets.map(_.instance)
      val path = mutated ++ heap.resolveDependencies(targets).flatMap(_.targets).flatMap(_.targets.map(_.instance))
      val collections = (path -- mutated).filter(instance => heap.isAlive(HeapElements(instance)))
      val bound = HeapTargetSet.from(collections.flatMap(heap.resolveReachableTargets(_).targets)).filter(target => !path(target.instance))

      bound.targets.toSeq.flatMap { target =>
        val dependencies = heap.resolveDependencies(HeapTargetSet(Set(target))).toSeq.filterNot(dependency => pendingResults(dependency.variable))
        val source = dependencies.find(dependency => dependency.targets.exists(_.targets.exists(holder => collections(holder.instance))))
        val others = dependencies.filterNot(dependency => source.exists(path => path == dependency || (path.accessors == dependency.accessors && path.targets.head == dependency.targets.head)))

        if (others.nonEmpty && (source.isEmpty || !others.forall(_.isDisjoint))) {
          throw AliasingAssignRewriteException.ambiguousAlias(tree)
        }

        others.map { other =>
          val holder = variable(tree, other.variable)

          Refresh(holder, rebuild(holder, other.accessors, read(variable(tree, source.get.variable), source.get.accessors)), condition(tree, other.condition))
        }
      }
    }

    def foreignRefreshes(tree: Expr, heap: HeapPointApproximation, receiver: Expr, targets: HeapTargetSet): Seq[Refresh] = {
      val own = pathOf(receiver)
      val foreign = heap.resolveDependencies(targets).toSeq
        .filterNot(dependency => own.exists { case (root, accessors) => dependency.variable == root.id && dependency.accessors == accessors })

      if (foreign.nonEmpty && (!targets.isDisjoint || !foreign.forall(_.isDisjoint))) {
        throw AliasingAssignRewriteException.ambiguousAlias(tree)
      }

      val refreshes = foreign.groupMapReduce(dependency => (dependency.variable, dependency.accessors))(_.condition)(_ ++ _).toSeq.map { case ((identifier, accessors), conditions) =>
        val holder = variable(tree, identifier)
        Refresh(holder, rebuild(holder, accessors, receiver), condition(tree, conditions))
      }

      refreshes ++ boundRefreshes(tree, heap, targets)
    }

    def mutation(tree: Expr, heap: HeapPointApproximation, receiver: Expr, mutated: Expr): Seq[Refresh] = {
      val targets = heap.resolveTargets(HeapApproximationAnalysis.resolveExpression(graph, heap, receiver))
      val ownRefresh = updated(receiver, mutated).map { case (holder, value) => Refresh(holder, value, condition(tree, always)) }

      ownRefresh.toSeq ++ foreignRefreshes(tree, heap, receiver, targets)
    }

    def writeBack(tree: Assignment, heap: HeapPointApproximation, target: Expr): Seq[Refresh] = {
      val targets = pathTargets(heap, target)
      val own = pathOf(target)
      val instances = targets.targets.map(_.instance)

      val reachable = targets.targets.flatMap(target => conjoin(target.conditions, heap.resolveReachableTargets(target.instance)))
      val inner = HeapTargetSet.from(reachable.filterNot(target => instances(target.instance)))

      val covering = heap.resolveDependencies(targets)
      val innerAliases = heap.resolveDependencies(inner)
        .filterNot(dependency => own.exists { case (root, accessors) => dependency.variable == root.id && dependency.accessors.startsWith(accessors) })
        .filterNot(dependency => covering.exists(covered => covered.variable == dependency.variable && dependency.accessors.startsWith(covered.accessors)))

      if (innerAliases.nonEmpty) {
        throw AliasingAssignRewriteException.innerAlias(tree)
      }

      Refresh(tree.v, tree.value, condition(tree, always)) +: foreignRefreshes(tree, heap, target, targets)
    }

    val own = graph.points.values.foldLeft(Map.empty[ExpressionID, Seq[Refresh]]) { (refreshes, point) =>
      (point.e, analysis.heapAt.get(point.id)) match {
        case (e @ (_: FieldAssignment | _: ArrayUpdate | _: MutableMapUpdate), None) =>
          refreshes + (ExpressionID(e) -> Seq.empty)

        case (e @ FieldAssignment(obj, selector, value), Some(heap)) =>
          refreshes + (ExpressionID(e) -> mutation(e, heap, obj, rebuildClass(obj, selector, value)))

        case (e @ ArrayUpdate(array, index, value), Some(heap)) =>
          refreshes + (ExpressionID(e) -> mutation(e, heap, array, ArrayUpdated(array, index, value).copiedFrom(e)))

        case (e @ MutableMapUpdate(map, key, value), Some(heap)) =>
          refreshes + (ExpressionID(e) -> mutation(e, heap, map, MutableMapUpdated(map, key, value).copiedFrom(e)))

        case (e @ WriteBack(target), Some(heap)) =>
          refreshes + (ExpressionID(e) -> writeBack(e, heap, target))

        case _ =>
          refreshes
      }
    }

    analysis.functions.values.collect { case function @ (_: LocalFunctionAnalysis | _: LambdaAnalysis) => function.analysis }.foldLeft(own)(_ ++ computeRefreshes(_))
  }

  def computeDistinctIndices(analysis: HeapApproximationAnalysis)(using symbols: Symbols): Map[ExpressionID, Seq[Expr]] = {
    val graph = analysis.graph

    def distinct(tree: Expr, indices: Iterable[(Expr, Expr)]): Seq[Expr] =
      indices.toSeq.distinct.map { case (first, second) => Not(Equals(first, second).copiedFrom(tree)).copiedFrom(tree) }

    def written(tree: Expr, heap: HeapPointApproximation, collection: Expr, index: Expr): Seq[Expr] =
      distinct(tree, heap.boundIndices(HeapApproximationAnalysis.resolveExpression(graph, heap, collection)).filterNot(_ == index).map(index -> _))

    def firstDifference(first: Seq[HeapAccessor], second: Seq[HeapAccessor]): Option[(Expr, Expr)] =
      first.zip(second).dropWhile { case (left, right) => left == right }.headOption.collect {
        case (ElementAccessor(left), ElementAccessor(right)) => left -> right
      }

    def arguments(tree: Expr, heap: HeapPointApproximation, args: Seq[Expr]): Seq[Expr] = {
      val dependencies = args.filter(arg => symbols.isMutableType(arg.getType)).map { arg =>
        heap.resolveDependencies(heap.resolveReachableTargets(HeapApproximationAnalysis.resolveExpression(graph, heap, arg))).toSeq
      }

      distinct(tree, for {
        i <- dependencies.indices
        j <- dependencies.indices
        if i < j
        first <- dependencies(i)
        second <- dependencies(j)
        if first.variable == second.variable
        indices <- firstDifference(first.accessors, second.accessors)
      } yield indices)
    }

    val own = graph.points.values.foldLeft(Map.empty[ExpressionID, Seq[Expr]]) { (conditions, point) =>
      (point.e, analysis.heapAt.get(point.id)) match {
        case (e: ArrayUpdate, Some(heap)) => conditions + (ExpressionID(e) -> written(e, heap, e.array, e.index))
        case (e: MutableMapUpdate, Some(heap)) => conditions + (ExpressionID(e) -> written(e, heap, e.map, e.key))
        case (e: ArrayUpdated, Some(heap)) if !CallResult.isWithin(e.value) => conditions + (ExpressionID(e) -> written(e, heap, e.array, e.index))
        case (e: MutableMapUpdated, Some(heap)) if !CallResult.isWithin(e.value) => conditions + (ExpressionID(e) -> written(e, heap, e.map, e.key))
        case (e: FunctionInvocation, Some(heap)) => conditions + (ExpressionID(e) -> arguments(e, heap, e.args))
        case (e: ApplyLetRec, Some(heap)) => conditions + (ExpressionID(e) -> arguments(e, heap, e.args))
        case (e: Application, Some(heap)) => conditions + (ExpressionID(e) -> arguments(e, heap, e.args))
        case _ => conditions
      }
    }

    analysis.functions.values.collect { case function @ (_: LocalFunctionAnalysis | _: LambdaAnalysis) => function.analysis }.foldLeft(own)(_ ++ computeDistinctIndices(_))
  }

  def computeBoundIdentifiers(body: Expr): Map[ExpressionID, Set[Identifier]] = {
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

  def computePromotions(refreshes: Map[ExpressionID, Seq[Refresh]]): Set[Identifier] =
    refreshes.values.flatten.map(_.holder.id).toSet

  def checkLambdaCaptures(body: Expr, promotions: Set[Identifier]): Unit = {
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
        if (captured.exists(id => promotions(id) || assigned(id))) throw AliasingAssignRewriteException.staleCapture(lambda)

      case _ =>
    }(body)
  }

  case class Transformer(
    refreshes: Map[ExpressionID, Seq[Refresh]],
    distinctIndices: Map[ExpressionID, Seq[Expr]],
    boundIdentifiers: Map[ExpressionID, Set[Identifier]],
    promotions: Set[Identifier]
  ) {
    private val declared: Set[Identifier] = boundIdentifiers.values.flatten.toSet

    def transform(body: Expr)(using Symbols): Expr = {
      def statement(tree: Expr, refresh: Refresh): Expr = {
        val bound = boundIdentifiers.getOrElse(ExpressionID(tree), Set.empty)
        if (exprOps.variablesOf(refresh.condition).exists(variable => declared(variable.id) && !bound(variable.id))) throw AliasingAssignRewriteException.conditionOutOfScope(tree)
        if (exprOps.variablesOf(refresh.value).exists(variable => declared(variable.id) && !bound(variable.id))) throw AliasingAssignRewriteException.keyOutOfScope(tree)

        val assignment = Assignment(refresh.holder, refresh.value).copiedFrom(tree)
        if (refresh.condition == BooleanLiteral(true)) assignment
        else IfExpr(refresh.condition, assignment, UnitLiteral().copiedFrom(tree)).copiedFrom(tree)
      }

      def asserted(tree: Expr, condition: Expr, rest: Expr): Expr = {
        val bound = boundIdentifiers.getOrElse(ExpressionID(tree), Set.empty)
        if (exprOps.variablesOf(condition).exists(variable => declared(variable.id) && !bound(variable.id))) throw AliasingAssignRewriteException.keyOutOfScope(tree)

        Assert(condition, Some("distinct collection indices"), rest).copiedFrom(tree)
      }

      object transformer extends ConcreteOOSelfTreeTransformer {
        override def transform(e: Expr): Expr =
          distinctIndices.getOrElse(ExpressionID(e), Seq.empty).foldRight(rewritten(e))(asserted(e, _, _))

        private def rewritten(e: Expr): Expr = refreshes.get(ExpressionID(e)) match {
          case Some(statements) =>
            super.transform(Block(statements.map(statement(e, _)), UnitLiteral().copiedFrom(e)).copiedFrom(e))

          case None => e match {
            case Let(vd, value, body) if promotions(vd.id) =>
              LetVar(vd.toVar, transform(value), transform(body)).copiedFrom(e)

            case LetVar(vd, value, body) if promotions(vd.id) && !vd.flags.contains(IsVar) =>
              LetVar(vd.toVar, transform(value), transform(body)).copiedFrom(e)

            case v: Variable if promotions(v.id) =>
              Variable(v.id, v.tpe, (v.flags :+ IsVar).distinct).copiedFrom(v)

            case _ =>
              super.transform(e)
          }
        }
      }

      transformer.transform(body)
    }
  }
}


class AliasingAssignRewrite(override val s: Trees)(override val t: s.type)(using override val context: inox.Context)
  extends oo.SimplePhase
     with IdentitySorts
     with oo.SimplyCachedClasses
     with oo.SimplyCachedTypeDefs
     with Transformations { self =>
  import s._

  override protected final val funCache = new ExtractionCache[s.FunDef, (FunctionResult, FunctionSummary)]((fd, context) =>
    getDependencyKey(fd.id)(using context.symbols)
  )

  protected class TransformerContext(override val s: self.s.type, override val t: s.type)
                                    (using val symbols: s.Symbols)
    extends oo.ConcreteTreeTransformer(s, t) {

    def freshenInstances(body: Expr): Expr =
      exprOps.postMap {
        case v: Variable => Some(Variable(v.id, v.tpe, v.flags).copiedFrom(v))
        case e =>
          val exprOps.Deconstructor(children, builder) = e: @unchecked
          Some(builder(children).copiedFrom(e))
      }(body)

    def preprocess(fd: FunDef): FunDef = {
      val (specs, bodyOpt) = exprOps.deconstructSpecs(fd.fullBody)
      fd.copy(fullBody = exprOps.reconstructSpecs(specs, bodyOpt.map(body => normalizeReceivers(freshenInstances(body))), fd.returnType)).copiedFrom(fd)
    }

    lazy val preprocessed: s.Symbols = symbols.withFunctions(symbols.functions.values.toSeq.map(preprocess))

    override def transform(fd: s.FunDef): t.FunDef = {
      given s.Symbols = preprocessed
      val (specs, bodyOpt) = exprOps.deconstructSpecs(preprocessed.getFunction(fd.id).fullBody)

      bodyOpt match {
        case None =>
          super.transform(fd)

        case Some(body) =>
          val analysis = HeapApproximationAnalysis.refineDefinition(fd.id, fd.params, body)
          HeapApproximationAnalysis.checkReturn(analysis, fd.params, body, imported = true)

          val refreshes = computeRefreshes(analysis)
          val distinctIndices = computeDistinctIndices(analysis)
          val boundIdentifiers = computeBoundIdentifiers(body)
          val promotions = computePromotions(refreshes)
          checkLambdaCaptures(body, promotions)

          val transformedBody = exprOps.postMap {
            case Annotated(inner, flags) if flags.exists(WriteBack.location(_).isDefined) => Some(Annotated(inner, flags.filter(WriteBack.location(_).isEmpty)))
            case _ => None
          }(Transformer(refreshes, distinctIndices, boundIdentifiers, promotions).transform(body))
          val transformedFullBody = exprOps.reconstructSpecs(specs, Some(transformedBody), fd.returnType)

          super.transform(fd.copy(fullBody = transformedFullBody).copiedFrom(fd))
      }
    }
  }

  override protected def getContext(syms: s.Symbols) = new TransformerContext(self.s, self.t)(using syms)
}

object AliasingAssignRewrite {
  def apply(tt: Trees)(using inox.Context): ExtractionPipeline {
    val s: tt.type
    val t: tt.type
  } = {
    class Impl(override val s: tt.type, override val t: tt.type) extends AliasingAssignRewrite(s)(t)

    new Impl(tt, tt)
  }
}
