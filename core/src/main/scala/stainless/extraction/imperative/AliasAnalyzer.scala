/* Copyright 2009-2020 EPFL, Lausanne */

package stainless
package extraction
package imperative

import scala.collection.mutable.{HashMap => MutableMap, HashSet => MutableSet}
import inox.utils.Position

trait AliasAnalyzer extends oo.CachingPhase {
  val s: Trees
  val t: s.type

  import s._
  import exprOps._

  protected type TransformerContext <: AliasAnalysis

  trait AliasAnalysis { self: TransformerContext =>
    implicit val symbols: s.Symbols

    private[imperative] val summaries: Summaries = {
      def updateStep(summaries: Summaries, fd: FunDef, iteration: Int): Summaries = {
        val dumpPath = Some(s"heapgraph_${fd.id}#$iteration.dot")
        val summary = computeSummary(summaries, fd, dumpPath)
        summaries.copy(functions = summaries.functions + (fd -> summary))
      }

      // The default call graph omits isolated functions, but we want all of them.
      val sccs = (symbols.callGraph ++ symbols.functions.keySet).stronglyConnectedComponents

      val res = sccs.topSort.reverse.foldLeft(Summaries.empty) { case (summaries, scc) =>
        // Fast path for the simple case of a single, non-recursive function
        if (scc.size == 1 && !symbols.isRecursive(scc.head)) {
          updateStep(summaries, symbols.getFunction(scc.head), 1)
        } else {
          val fds = scc.map(symbols.getFunction(_))
          val emptySummariesForScc = Summaries(fds.map(_ -> Summary(Map.empty)).toMap)
          var iteration = 0
          inox.utils.fixpoint[Summaries] { summaries =>
            iteration += 1
            fds.foldLeft(summaries)(updateStep(_, _, iteration))
          } (summaries merge emptySummariesForScc)
        }
      }

      println(s"\n=== SUMMARIES ===\n${res.asString}\n")
      res
      // null
    }
  }

  // Helpers

  // Whether the given type is relevant for a heap graph (whether it can point to other objects)
  def isHeapType(tpe: Type): Boolean = tpe match {
    case _: ADTType | _: ClassType | _: TupleType => true
    case _: UnitType | _: BooleanType | _: IntegerType | _: BVType | _: CharType => false
    // TODO: Handle other types
  }

  def isHeapParam(vd: ValDef): Boolean =
    isHeapType(vd.tpe)

  def getEscapingParams(fd: FunDef): Seq[ValDef] =
    fd.params.filter(isHeapParam)

  def getReturnType(fd: FunDef): Type = {
    val escapingParams = getEscapingParams(fd)
    tupleTypeWrap(fd.returnType +: escapingParams.map(_.tpe))
  }

  lazy val True = BooleanLiteral(true)
  lazy val False = BooleanLiteral(false)
  lazy val ResultId = FreshIdentifier("RES")
  lazy val FirstOrigin = FreshIdentifier("<first>")

  lazy val tupleFieldIds = (1 to 16).map(i => FreshIdentifier(s"_$i"))

  // Data structures

  case class Summaries(functions: Map[FunDef, Summary]) {
    def asString(implicit printerOpts: PrinterOptions): String = {
      val funs = functions.map { case (fd, sum) =>
        val caps = sum.capturedBy.map { case (captive, captors) =>
          s"${captive.id} <- ${captors.map(_.id).mkString(", ")}"
        }
        s"  ${fd.id}: {${caps.mkString("; ")}}"
      }
      s"functions:\n${funs.mkString("\n")}"
    }

    def merge(that: Summaries) =
      Summaries(functions ++ that.functions)
  }

  object Summaries {
    val empty = Summaries(Map.empty)
  }

  // For every parameter, we approximate whether, and if so, where the original object was captured
  case class Summary(capturedBy: Map[ValDef, Set[ValDef]])

  // case class AliasSummary(captures: Map[ValDef, CaptureStatus])
  // // A lattice of capture statuses.
  // // - NotCaptured: the parameter is unaliased after the function returns
  // // - CapturedBy(vds): aliased by any of the given bindings (parameters or the return value)
  // // - Unknown: aliased in some way we can't express
  // sealed abstract class CaptureStatus
  // case object NotCaptured extends CaptureStatus
  // case object Unknown extends CaptureStatus
  // case class CapturedBy(vds: Set[ValDef]) extends CaptureStatus

  // An accessor
  sealed abstract class Accessor {
    def id: Identifier

    // Returns the class field on the given type, if any
    def fieldOn(recvTpe: Type)(implicit symbols: Symbols): Option[ValDef] =
      (this, recvTpe) match {
        case (ADTAccessor(id), at: ADTType) =>
          at.getSort.constructors.flatMap(_.fields).find(_.id == id)
        case (ClassAccessor(id), ct: ClassType) =>
          symbols.getClassField(ct, id)
        case (TupleAccessor(index), TupleType(tps)) =>
          if (0 <= index && index < tps.length) Some(ValDef(this.id, tps(index))) else None
        case _ => None
      }

    def yieldsHeapTypeOn(recvTpe: Type)(implicit symbols: Symbols): Boolean =
      fieldOn(recvTpe).map(f => isHeapType(f.tpe)).getOrElse(false)
  }
  case class ADTAccessor(id: Identifier) extends Accessor
  case class ClassAccessor(id: Identifier) extends Accessor
  case class TupleAccessor(index: Int) extends Accessor {
    def id: Identifier = tupleFieldIds(index)
  }

  // A sequence of accessors
  case class Path(path: Seq[Accessor])

  // A symbolic heap object (NOT a program binding)
  case class Object(vd: ValDef) {
    require(isHeapType(vd.tpe))

    override def toString: String = s"Object#${vd.id}"
  }

  object Object {
    def fresh(name: String, tpe: Type): Object = Object(ValDef(FreshIdentifier(name), tpe))

    def freshForAccessor(obj: Object, accessor: Accessor)(implicit symbols: Symbols): Object = {
      val field = accessor.fieldOn(obj.vd.tpe).get
      fresh(s"${obj.vd.id.name}.${field.id.name}", field.tpe)
    }
  }

  // The target of a reference, i.e, the object pointed to depending on the path condition.
  // Generally, Targets found in the core data structures (such as Graph) should always partition
  // the state space, i.e., `\/_i cond_i = true` and `forall i,j. cond_i /\ cond_j = false`.
  // However, this invariant may be broken for targets produced by intermediate operations.
  case class Target(pairs: Seq[(Expr, Object)]) {
    def toSeq: Seq[(Expr, Object)] = pairs
    lazy val objects: Seq[Object] = pairs.map(_._2)
    def objectSet: Set[Object] = objects.toSet

    def flatMap(f: Object => Target): Target = {
      val targetPairs = this.toSeq.flatMap { case (cond, obj) =>
        f(obj).toSeq.map { case (innerCond, innerObj) => (and(cond, innerCond), innerObj) }
      }
      Target(targetPairs)
    }

    def conditional(extraCond: Expr)(implicit symbols: Symbols): Target = {
      assert(extraCond.getType == BooleanType())
      extraCond match {
        case BooleanLiteral(true) => this
        case BooleanLiteral(false) => Target.empty
        case _ =>
          val adaptedTargetPairs = this.toSeq.map { case (cond, obj) =>
            (symbols.simplifyByConstructors(and(extraCond, cond)), obj)
          } .filter {
            case (BooleanLiteral(false), _) => false
            case _ => true
          }
          Target(adaptedTargetPairs)
      }
    }

    def ++(that: Target): Target =
      if (this.pairs.isEmpty) that
      else if (that.pairs.isEmpty) this
      else Target(this.pairs ++ that.pairs)

    def replace(subst: Map[Object, Object]): Target =
      if (pairs.exists(p => subst.contains(p._2)))
        Target(pairs.map(p => (p._1, subst.getOrElse(p._2, p._2))))
      else
        this
  }

  object Target {
    def apply(obj: Object): Target = Target(Seq((True, obj)))

    val empty = Target(Seq.empty)
  }

  type Origin = Identifier

  // A graph representing a heap state and bindings into it symbolically
  case class Graph(
    objects: Set[Object],
    contents: Map[Object, Map[Accessor, Target]],
    blockedBy: Map[Object, Set[Object]], // for a captured object, its potential captors
    bindings: Map[ValDef, Target], // mapping from program bindings to heap objects
    escaped: Set[Object], // objects that escaped and we thus must give up access to
    initialContents: MutableMap[(Object, Accessor), Object]
  ) {
    def withObject(obj: Object): Graph =
      this.copy(objects = objects + obj, contents = contents + (obj -> Map.empty))

    def withBinding(vd: ValDef, target: Target): Graph =
      this.copy(bindings = bindings + (vd -> target))

    def withContent(obj: Object, accessor: Accessor, target: Target): Graph =
      this.copy(contents = Graph.updatedContents(contents, obj, accessor, target))
    def withContent(entries: Seq[(Object, Target)], accessor: Accessor): Graph =
      this.copy(contents = entries.foldLeft(contents) { case (cs, (obj, target)) =>
        Graph.updatedContents(cs, obj, accessor, target)
      })

    def withContents(obj: Object, targets: Map[Accessor, Target]): Graph =
      this.copy(contents = contents + (obj -> targets))

    def havoc(objs: Set[Object]): Graph = {
      assert(objs.subsetOf(this.objects))
      val newContents = contents ++ objs.map(_ -> Map.empty[Accessor, Target])
      this.copy(contents = newContents)
    }

    def withEscaped(objs: Set[Object]): Graph =
      havoc(objs).copy(escaped = escaped ++ objs)

    def isInvalidBinding(bdg: ValDef): Boolean =
      (computeReachable(bindings(bdg).objectSet) intersect escaped).nonEmpty

    // Ensures that we have explicit objects representing the values accessible at `accessor` of
    // all `objects`.
    // For each unexpanded accessor, we create a fresh object and target it unconditionally.
    def ensureObjectsUnfoldedAt(recvObjs: Seq[Object], accessor: Accessor)(
        implicit symbols: Symbols): Graph =
    {
      var newObjects = this.objects
      var newContents = this.contents

      val missing = recvObjs.filterNot(obj => contents(obj).contains(accessor))
      missing.foreach { recvObj =>
        val newObj = initialContents.getOrElseUpdate((recvObj, accessor), {
          Object.freshForAccessor(recvObj, accessor)
        })
        newObjects = newObjects + newObj
        newContents = newContents + (newObj -> Map.empty)
        newContents = Graph.updatedContents(newContents, recvObj, accessor, Target(newObj))
      }
      this.copy(objects = newObjects, contents = newContents)
    }

    // Replace existing objects in blockedBy and various targets by fresh objects
    def replaceByFresh(subst: Map[Object, Object]): Graph = {
      if (subst.isEmpty)
        return this

      val freshObjects = subst.values.toSet
      assert((objects intersect freshObjects).isEmpty)

      val newObjects = objects ++ freshObjects

      // TODO: This could be much faster if we had back edges
      val newContents = contents ++ contents.toSeq.flatMap { case (obj, content) =>
        val changedContent = content.toSeq.flatMap { case (accessor, target) =>
          val changedTarget = target.replace(subst)
          if (target ne changedTarget) Some(accessor -> changedTarget) else None
        }
        if (changedContent.nonEmpty) Some(obj -> (content ++ changedContent)) else None
      } ++ freshObjects.map(_ -> Map.empty[Accessor, Target])

      assert((blockedBy.keySet intersect subst.keySet).isEmpty)
      val newBlockedBy = blockedBy ++ blockedBy.toSeq.flatMap { case (captive, captors) =>
        if (captors.exists(subst.contains))
          Some(captive -> captors.map(obj => subst.getOrElse(obj, obj)))
        else
          None
      }

      val newBindings = bindings ++ bindings.toSeq.flatMap { case (bdg, target) =>
        val changedTarget = target.replace(subst)
        if (target ne changedTarget) Some(bdg -> changedTarget) else None
      }

      this.copy(objects = newObjects, contents = newContents, blockedBy = newBlockedBy,
        bindings = newBindings)
    }

    // Find all the transitively reachable objects starting from a given set of objects
    // TODO: Use a path condition to allow computing the precise set
    def computeReachable(initialObjects: Set[Object]): Set[Object] =
      inox.utils.fixpoint[Set[Object]](objects => {
        objects ++ objects.flatMap { obj =>
          this.contents(obj).values.flatMap(_.objectSet)
        }
      })(initialObjects)

    // Find all the transitively reachable objects starting from the given targets
    // TODO: Cut down the initialObjects set by using the path condition
    def computeReachable(targets: Seq[Target]): Set[Object] = {
      val initialObjects = targets.flatMap(target => target.objects)
      computeReachable(initialObjects.toSet)
    }
  }

  object Graph {
    private def updatedContents(contents: Map[Object, Map[Accessor, Target]], obj: Object,
        accessor: Accessor, target: Target) = {
      val newObjContents = contents(obj) + (accessor -> target)
      contents + (obj -> newObjContents)
    }
  }

  // A mapping from a binding to a target within a graph
  type BindingTarget = (ValDef, Target)

  // Graph and summary computation

  private[this] def computeSummary(summaries: Summaries, fd: FunDef, dumpPath: Option[String])(
    implicit symbols: Symbols): Summary =
  {
    val ctx = context
    import symbols._

    // Ensure the graph has explicit objects for accessing `accessor` on `expr`
    def prepareForAccess(g: Graph, recvTarget: Target, accessor: Accessor): Graph = {
      // val missing = recvTarget.objects.filterNot(obj => g.contents(obj).contains(accessor))
      // if (missing.nonEmpty) {
      //   ctx.reporter.fatalError(pos,
      //     s"Not all receiver object(s) unfolded at accessor $accessor! " +
      //     "You can work around this by adding bindings for intermediate results.")
      // }
      g.ensureObjectsUnfoldedAt(recvTarget.objects, accessor)
    }

    // Computes the new contents on objects assuming we update `accessor` on `recvTargets`
    // TODO: Try to eliminate targets using the path condition and a simplifier or solver?
    def update(g: Graph, recvTarget: Target, accessor: Accessor, valueTarget: Target): Graph =
    {
      // Gather the conditions under which each receiver object will be modified
      val updateConds = recvTarget.toSeq.foldLeft(Map.empty[Object, Seq[Expr]]) {
        case (map, (cond, recvObj)) =>
          map + (recvObj -> (cond +: map.getOrElse(recvObj, Seq.empty)))
      }

      // Compute updated targets for each recvObj#accessor
      val updates = updateConds.toSeq.map { case (recvObj, updateConds) =>
        // The condition under which this receiver will be updated
        val updateCond = simplifyByConstructors(orJoin(updateConds))

        // Retain part of old target that isn't obviously overwritten and update its conditions
        val oldTarget = g.contents(recvObj)(accessor).conditional(not(updateCond))

        // Make the value target conditional on the updateCond
        val newTarget = valueTarget.conditional(updateCond)

        (recvObj, oldTarget ++ newTarget)
      }

      g.withContent(updates, accessor)
    }

    // Check that none of the targets overlap
    def checkArgumentsDisjoint(g: Graph, argTargets: Seq[Target], pos: Position): Unit = {
      for {
        (t1, i) <- argTargets.zipWithIndex
        t2 <- argTargets.drop(i+1)
        both = g.computeReachable(t1.objectSet) intersect g.computeReachable(t2.objectSet)
        bothStr = both.map(_.vd.toString).mkString(", ")
      } ctx.reporter.fatalError(pos, s"Objects {$bothStr} are aliased in function invocation")
    }

    // Record whether and by whom the objects underlying the given bindings are captured
    def capture(g: Graph, captures: Seq[(Seq[Target], Target)]): Graph =
      captures.foldLeft(g) { case (g, (captorTargets, captiveTarget)) =>
        val captors = captorTargets.foldLeft(Set.empty[Object])(_ ++ _.objectSet)
        val captives = captiveTarget.objectSet

        // Record who captured what, so we can perhaps release the captives later
        assert((g.blockedBy.keySet intersect captives).isEmpty)
        g.copy(blockedBy = g.blockedBy ++ captives.map(_ -> captors))
      }

    // Get the unfolded graph resulting from a set of read accesses
    def replayUnfolds(g: Graph, unfoldedPairs: Seq[(Object, Accessor)]): Graph = {
      val unfolded: Map[Object, Seq[Accessor]] = unfoldedPairs
        .groupBy(_._1).toMap.mapValues(_.map(_._2))
      var candidates = unfolded.keySet
      var objects = g.objects
      var contents = g.contents
      var continue = true
      while (continue) {
        val replayable = candidates intersect objects
        if (replayable.nonEmpty) {
          contents = contents ++ replayable.map { case obj =>
            val currentContent = contents(obj)
            val newContent = unfolded(obj)
              .filter(accessor => !currentContent.contains(accessor))
              .map { accessor =>
                val newObj = g.initialContents((obj, accessor))
                objects = objects + newObj
                accessor -> Target(newObj)
              }
            obj -> (currentContent ++ newContent)
          }
          candidates = candidates diff replayable
        } else {
          continue = false
        }
      }
      g.copy(objects = objects, contents = contents)
    }

    def mergeGraphs(gA: Graph, gB: Graph, cond: Expr): Graph = {
      // TODO: The equality checks among targets could be weakened further. We could also try to
      // limit the traversal by tracking what changed in the graphs of each branch.
      val condNeg = not(cond)

      def intersectionMaps[K, V](mapA: Map[K, V], mapB: Map[K, V])(f: (V, V) => V): Map[K, V] =
        (mapA.keySet intersect mapB.keySet).foldLeft(Map.empty[K, V]) { case (map, key) =>
          map + (key -> f(mapA(key), mapB(key)))
        }

      def intersectionTargets[K](mapA: Map[K, Target], mapB: Map[K, Target]): Map[K, Target] =
        intersectionMaps(mapA, mapB)((tA, tB) =>
          if (tA == tB) tA else tA.conditional(cond) ++ tB.conditional(condNeg))

      def unionMaps[K, V](mapA: Map[K, V], mapB: Map[K, V])(
          f: (Option[V], Option[V]) => V): Map[K, V] =
        (mapA.keySet union mapB.keySet).foldLeft(Map.empty[K, V]) { case (map, key) =>
          map + (key -> f(mapA.get(key), mapB.get(key)))
        }

      def unionTargets[K](mapA: Map[K, Target], mapB: Map[K, Target]): Map[K, Target] =
        unionMaps(mapA, mapB)((tA, tB) =>
          if (tA == tB) tA.get else tA.getOrElse(Target.empty).conditional(cond) ++
            tB.getOrElse(Target.empty).conditional(condNeg))

      val objects = gA.objects union gB.objects
      val contents = unionMaps(gA.contents, gB.contents)((a, b) =>
        unionTargets(a.getOrElse(Map.empty), b.getOrElse(Map.empty)))
      val blockedBy = unionMaps(gA.blockedBy, gB.blockedBy)((a, b) =>
        a.getOrElse(Set.empty) union b.getOrElse(Set.empty))
      val bindings = intersectionTargets(gA.bindings, gB.bindings)
      val escaped = gA.escaped union gB.escaped
      assert(gA.initialContents eq gB.initialContents)
      val initialContents = gA.initialContents

      Graph(objects, contents, blockedBy, bindings, escaped, initialContents)
    }

    // Release the underlying objects by making its captors escape
    def ensureRecovered(g: Graph, target: Target, pos: Position): Graph = {
      val targetObjs = g.computeReachable(target.objectSet)
      val escaped = targetObjs intersect g.escaped
      val captives = targetObjs intersect g.blockedBy.keySet
      if (escaped.nonEmpty) {
        val objsStr = escaped.mkString(", ")
        ctx.reporter.fatalError(pos, s"Reference to escaped objects {$objsStr}")
      } else if (captives.nonEmpty) {
        val captors = captives.flatMap(g.blockedBy)
        g.withEscaped(g.computeReachable(captors))
      } else {
        g
      }
    }

    // The actual computation of the heap graph

    def rec(g: Graph, expr: Expr): (Graph, Option[Target]) = {
      // Add a new object of the given typen and with the given subobjects to the graph
      def construct(g: Graph, tpe: Type, fields: Seq[(Type, Accessor)],
          args: Seq[Expr]): (Graph, Object) =
      {
        val obj = Object.fresh("fresh", tpe)
        val (g1, argTargets) = recSequential(g, args)
        val contents = fields.zip(argTargets).foldLeft(Map.empty[Accessor, Target]) {
          case (cs, ((tpe, acc), Some(target))) if isHeapType(tpe) => cs + (acc -> target)
          case (cs, _) => cs
        }
        (g1.withObject(obj).withContents(obj, contents), obj)
      }

      // Select the subobject based on the given accessor
      def select(g: Graph, recv: Expr, accessor: Accessor): (Graph, Option[Target]) = {
        val (g1, recvTargetOpt) = rec(g, recv)
        if (accessor.yieldsHeapTypeOn(recv.getType)) {
          val recvTarget = recvTargetOpt.get
          val g2 = prepareForAccess(g1, recvTarget, accessor)
          val accTarget = recvTarget.flatMap(g2.contents(_)(accessor))
          (g2, Some(accTarget))
        } else {
          (g1, None)
        }
      }

      def recSequential(g: Graph, exprs: Seq[Expr]): (Graph, Seq[Option[Target]]) =
        exprs.foldLeft((g, Seq.empty[Option[Target]])) { case ((ga, targets), expr) =>
          val (gb, target) = rec(ga, expr)
          (gb, target +: targets)
        }

      expr match {
        case v: Variable =>
          g.bindings.get(v.toVal) match {
            case targetOpt @ Some(target) =>
              val g1 = ensureRecovered(g, target, v.getPos)
              (g1, Some(target))
            case None =>
              assert(!isHeapType(v.tpe), s"Expected heap graph binding for $v : ${v.tpe}")
              (g, None)
          }

        case Let(vd, value, body) =>
          val (g1, valueTargetOpt) = rec(g, value)
          val g2 = valueTargetOpt.map(g1.withBinding(vd, _)).getOrElse(g1)
          rec(g2, body)

        case Block(exprs, lastExpr) =>
          val g1 = exprs.foldLeft(g) { case (g, expr) => rec(g, expr)._1 }
          rec(g1, lastExpr)

        case expr: ADT =>
          val fields = expr.getConstructor.fields.map(f => f.tpe -> ADTAccessor(f.id))
          val (g1, obj) = construct(g, expr.getType, fields, expr.args)
          (g1, Some(Target(obj)))

        case ClassConstructor(ct, args) =>
          val fields = ct.tcd.fields.map(f => f.tpe -> ClassAccessor(f.id))
          val (g1, obj) = construct(g, ct, fields, args)
          (g1, Some(Target(obj)))

        case Tuple(args) =>
          val fields = args.zipWithIndex.map(ai => ai._1.getType -> TupleAccessor(ai._2))
          val (g1, obj) = construct(g, expr.getType, fields, args)
          (g1, Some(Target(obj)))

        case ADTSelector(recv, field) =>
          select(g, recv, ADTAccessor(field))

        case ClassSelector(recv, field) =>
          select(g, recv, ClassAccessor(field))

        case TupleSelect(recv, index) =>
          select(g, recv, TupleAccessor(index - 1))

        case FieldAssignment(recv, field, value) =>
          // FIXME: Prevent introduction of cycles?
          val accessor = ClassAccessor(field)
          if (accessor.yieldsHeapTypeOn(recv.getType)) {
            val (g1, Some(recvTarget)) = rec(g, recv)
            val g2 = prepareForAccess(g1, recvTarget, accessor)
            val (g3, Some(valueTarget)) = rec(g2, value)
            val g4 = update(g3, recvTarget, accessor, valueTarget)
            (g4, None) // returns Unit, so no heap object
          } else {
            val (g1, _) = rec(g, recv)
            val (g2, _) = rec(g1, value)
            (g2, None)
          }

        // case fi: FunctionInvocation if !symbols.isRecursive(fi.id) =>
        //   exprOps.withoutSpecs(symbols.simplifyLets(fi.inlined))
        //     .map(rec(g, _))
        //     .getOrElse(???)

        case fi: FunctionInvocation =>
          val fd = fi.tfd.fd
          val calleeSummary = summaries.functions(fd)

          val (g1, argTargets) = recSequential(g, fi.args)

          // Ensure no objects are aliased through function arguments
          checkArgumentsDisjoint(g1, argTargets.flatten, fi.getPos)

          // Mark all objects reachable from the heap-relevant arguments as escaped
          // TODO: Don't let pure parameters escape
          val g2 = g1.withEscaped(g1.computeReachable(argTargets.flatten))

          // Replace escaping objects
          val argObjsSubst = fd.params.zip(argTargets).foldLeft(Map.empty[Object, Object]) {
            case (subst, (param, Some(target))) =>
              val newObj = Object(param.freshen)
              subst ++ target.objects.map(obj => obj -> newObj)
            case (subst, (_, None)) => subst
          }
          val g3 = g2.replaceByFresh(argObjsSubst)

          // Add new object returned from the call
          val returnTpe = fi.getType
          val (g4, resTargetOpt) = if (isHeapType(returnTpe)) {
            val returnObj = Object.fresh("ret", returnTpe)
            (g3.withObject(returnObj), Some(Target(returnObj)))
          } else {
            (g3, None)
          }

          // Record captured objects
          val argTargetsRewritten = argTargets.map(_.map(_.replace(argObjsSubst)))
          val paramsAndArgTargets = fd.params.zip(argTargetsRewritten)
          val argTargetsMap: Map[ValDef, Option[Target]] = (
              paramsAndArgTargets ++
              resTargetOpt.map(resTarget => (ValDef(ResultId, returnTpe), Some(resTarget))).toSeq
            ).toMap
          val captures = paramsAndArgTargets.collect {
            case (param, Some(argTarget)) if calleeSummary.capturedBy.contains(param) =>
              (calleeSummary.capturedBy(param).toSeq.flatMap(argTargetsMap.apply), argTarget)
          }
          val g5 = capture(g4, captures)

          (g5, resTargetOpt)

        case IfExpr(cond, thenn, elze) =>
          // TODO: We need to somehow capture `cond` as interpreted at *this* program point
          // (to reflect the current state of its mutable parts).
          val (g1, _) = rec(g, cond)

          // Process each branch, while keeping track of which objects were unfolded
          def unfoldsSnapshot(): Set[(Object, Accessor)] = g.initialContents.keySet.toSet
          val unfoldsBase = unfoldsSnapshot()
          val (g2A, targetOptA) = rec(g1, thenn)
          val unfoldsAfterA = unfoldsSnapshot()
          val (g2B, targetOptB) = rec(g1, elze)
          val unfoldsAfterB = unfoldsSnapshot()

          // Make sure that if one branch unfolds an object, so does the other
          // This ensures that targets will remain exhaustive after the merging step below
          val (unfoldsA, unfoldsB) =
            (unfoldsAfterA diff unfoldsBase, unfoldsAfterB diff unfoldsAfterA)
          val g3A = replayUnfolds(g2A, unfoldsB.toSeq)
          val g3B = replayUnfolds(g2B, unfoldsA.toSeq)

          // Compute the overall returned target
          val targetOpt = (targetOptA, targetOptB) match {
            case (Some(targetA), Some(targetB)) =>
              if (targetA == targetB)
                Some(targetA)
              else
                Some(targetA.conditional(cond) ++ targetB.conditional(not(cond)))
            case (None, None) =>
              None
            case _ => ctx.reporter.internalError("Computing heap graph for if expression " +
              "returned target in one but not the other branch")
          }
          (mergeGraphs(g3A, g3B, cond), targetOpt)

        case m: MatchExpr =>
          rec(g, matchToIfThenElse(m))

        // Mundane cases

        case _: Literal[_] =>
          // Literals are not heap objects
          (g, None)

        case Equals(lhs, rhs) =>
          val (g1, _) = rec(g, lhs)
          val (g2, _) = rec(g1, rhs)
          (g2, None)

        case IsInstanceOf(e, _) => (rec(g, e)._1, None)
        case AsInstanceOf(e, _) => rec(g, e)
        case Assert(_, _, e) => (rec(g, e)._1, None)
        case Annotated(e, _) => rec(g, e)

        case _ =>
          val kind = expr.getClass.getName
          ctx.reporter.fatalError(s"Unsupported expr of kind $kind: $expr")
      }
    }

    val inputs = fd.params
    val body = exprOps.withoutSpecs(fd.fullBody).getOrElse(???)

    // Create the initial graph containing only the inputs
    val (contentsSeq, bindingsSeq) = inputs
      .filter(isHeapParam)
      .map { input =>
        val obj = Object(input.freshen)
        (obj -> Map.empty[Accessor, Target], input -> Target(obj))
      }
      .unzip
    val (contents, bindings) = (contentsSeq.toMap, bindingsSeq.toMap)
    val graph = Graph(contents.keySet, contents, Map.empty, bindings, Set.empty, MutableMap.empty)

    // Compute the graph at the end of the function
    val (resultGraph, resultTargetOpt) = rec(graph, body)
    val resultOpt = resultTargetOpt.map(target => (ValDef(ResultId, body.getType), target))

    // Dump the graph to dot
    dumpPath.foreach(dumpGraph(resultGraph, resultOpt, _))

    // Compute the actual captures
    val capturedByActual = {
      // TODO: Do this more efficiently by walking up back edges of bindings' objects
      val capturedBy: Map[ValDef, MutableSet[ValDef]] =
        graph.bindings.keys.map(_ -> MutableSet.empty[ValDef]).toMap
      val paramBindings = fd.params
        .filter(resultGraph.bindings.contains)
        .map(p => p -> resultGraph.bindings(p))
      (paramBindings ++ resultOpt).foreach {
        case (captorBdg, captorBdgTarget) =>
          val captorReach = resultGraph.computeReachable(captorBdgTarget.objectSet)

          // FIXME: Probably not actually true, but where do we want to represent this?
          assert(resultGraph.escaped.intersect(captorReach).isEmpty)

          for {
            (captiveBdg, captiveBdgTarget) <- paramBindings
            if captiveBdg ne captorBdg
            captiveReach = resultGraph.computeReachable(captiveBdgTarget.objectSet)
            if (captorReach intersect captiveReach).nonEmpty
          } capturedBy(captiveBdg) += captorBdg
      }
      capturedBy
        .filter { case (_, mset) => mset.nonEmpty }
        .mapValues(_.toSet)
    }

    // Extract the prescribed captures, if any
    // TODO: Come up with a more integrated solution than this (e.g. like `old` in post conditions)
    val capturedByExpected = {
      def bindingByName(name: String): ValDef =
        if (name == ResultId.name)
          resultOpt.map(_._1).getOrElse(ctx.reporter.fatalError(
            "Referred to result parameter 'RES' in a function that doesn't return a heap object"))
        else
          resultGraph.bindings.keys
            .find(b => b.id.name == name)
            .getOrElse(ctx.reporter.fatalError(s"Referred to unknown parameter '$name'"))

      var hasSpecs = false
      val specs = fd.flags.flatMap { case Annotation("capturedBy", args) =>
        hasSpecs = true
        val specsStr = args.headOption match {
          case Some(StringLiteral(s)) => s
          case _ => ctx.reporter.fatalError("Single string expected as captured-by spec")
        }
        if (specsStr.nonEmpty)
          specsStr.split(';').map { specStr =>
            val specParts = specStr.split("<-").toSeq
            if (specParts.length < 1 || specParts.length > 2)
              ctx.reporter.fatalError("Illegal captured-by spec")
            val captive = bindingByName(specParts(0).trim)
            val captors =
              if (specParts.length == 1) Set.empty[ValDef]
              else specParts(1).split(',').map(n => bindingByName(n.trim)).toSet
            captive -> captors
          }
        else
          Seq.empty
      }
      if (hasSpecs) {
        val specsMap = specs.toMap
        if (specs.size != specsMap.size)
          ctx.reporter.fatalError("Captive was specified more than once in captured-by spec")
        val specsMapClosed = inox.utils.GraphOps.transitiveClosure(specsMap)
          .map { case (captive, captors) => captive -> (captors - captive) }
        Some(specsMapClosed)
      } else {
        None
      }
    }

    // Check if capturedBy sets match
    val capturedBy: Map[ValDef, Set[ValDef]] = capturedByExpected match {
      case Some(exp) =>
        def capturesAsString(captures: Map[ValDef, Set[ValDef]]): String =
          captures.toSeq
            .sortBy(_._1)
            .map(c => s"${c._1.id.name} <- ${c._2.map(_.id.name).mkString(", ")}")
            .mkString("; ")
        if (exp != capturedByActual)
          ctx.reporter.fatalError(
            s"Captured-by sets don't match:\n\tExpected: ${capturesAsString(exp)}\n\t" +
            s"Actual: ${capturesAsString(capturedByActual)}")
        exp
      case None => capturedByActual
    }

    Summary(capturedBy)
  }

  private[this] def dumpGraph(graph: Graph, resultOpt: Option[BindingTarget], path: String,
      showContainers: Boolean = false): Unit =
  {
    import java.nio.file.{Files, Paths}

    def isInvalidBinding(bdg: ValDef) =
      resultOpt match {
        case Some((resVd, _)) if resVd eq bdg => false
        case _ => graph.isInvalidBinding(bdg)
      }

    // println(s" --- Function ${fd.id}: ---")
    // println(s"OBJECTS: ${graph.objects}")
    // println(s"CONTENTS: ${graph.contents}")

    // Describe graph in DOT syntax
    def I(id: Identifier) = id.uniqueName.toString.replace('$', '_').replace(".", "__")
    def N(id: Identifier) = id.toString
    def O(opts: Seq[String]) = s"[${opts.mkString(", ")}]"

    def trim(s: String, maxLength: Int = 20) =
      if (s.length > maxLength) s.slice(0, maxLength-3) + "..." else s
    def redOpt(cond: Boolean) = if (cond) Some("color=crimson") else None

    def describeTarget(src: String, target: Target, opts: Seq[String] = Seq.empty): String = {
      target.toSeq.map { case (cond, recv) =>
        val lblOpts = if (cond == True) Seq.empty
          else Seq(s"""taillabel="${trim(cond.toString)}"""", "labelfontsize=10")
        val allOpts = lblOpts ++ opts
        s"""$src -> obj_${I(recv.vd.id)} ${O(allOpts)}"""
      } .mkString("\n")
    }

    val objects = graph.objects.map { obj =>
      // Object name and record fields
      val fields = graph.contents(obj)
      val fieldsStr = if (fields.nonEmpty) {
        fields.keys.toSeq.sortBy(_.id).map(f => s"<${I(f.id)}> ${N(f.id)}").mkString("|")
      } else ""
      val lblOpt = s"""label="{${N(obj.vd.id)} | {$fieldsStr}}""""

      // Mark escaped objects
      val escapedOpt = redOpt(graph.escaped.contains(obj))

      val allOpts = Seq(lblOpt) ++ escapedOpt
      s"""obj_${I(obj.vd.id)} ${O(allOpts)}"""
    }

    val contents = graph.contents.toSeq.flatMap { case (obj, fields) =>
      fields.map { case (field, target) =>
        describeTarget(s"obj_${I(obj.vd.id)}:${I(field.id)}", target)
      }
    }

    // TODO: Output containers
    val containers = if (showContainers) { ??? } else Seq.empty[String]

    val bindingsAndResult = graph.bindings ++ resultOpt
    val bindings = bindingsAndResult.keys.map { bdg =>
      val opts = Seq(s"""label="${N(bdg.id)}"""", """style="bold,rounded"""")
      val allOpts = opts ++ redOpt(isInvalidBinding(bdg))
      s"""bdg_${I(bdg.id)} ${O(allOpts)}"""
    }
    val bindingEdges = bindingsAndResult.map { case (bdg, target) =>
      val opts = Seq("style=bold") ++ redOpt(isInvalidBinding(bdg))
      describeTarget(s"bdg_${I(bdg.id)}", target, opts)
    }

    val output = s"""digraph heapgraph {
    |node [shape = record,height=.1];
    |
    |${objects.mkString("\n")}
    |${contents.mkString("\n")}
    |${containers.mkString("\n")}
    |
    |${bindings.mkString("\n")}
    |${bindingEdges.mkString("\n")}
    |}""".stripMargin

    // Write to file
    val path_ = Paths.get(path)
    Files.write(path_, output.getBytes())
  }
}
