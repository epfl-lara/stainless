/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package imperative

import scala.annotation.tailrec

trait HeapApproximationGraphs extends HeapApproximationPoints {
  import s._
  import s.exprOps.Deconstructor

  /** A node of the graph: the expression `e`, the scope it runs in, and the variables live after it. */
  case class ProgramPoint(scope: Int, e: Expr, live: Set[Identifier] = Set.empty) {
    /** The id of the expression of this point. */
    def id: ExpressionID = ExpressionID(e)
  }

  /** The control flow of a function body, from `entrypoint` to `exitpoint`, with one point per expression. */
  case class HeapApproximationGraph private (
    params: Seq[ValDef],

    entrypoint: ExpressionID,
    exitpoint: ExpressionID,
    points: Map[ExpressionID, ProgramPoint],

    parents: Map[ExpressionID, Set[ExpressionID]],
    transitions: Map[ExpressionID, Set[ExpressionID]],
  ) {
    /** The scope of `point`. */
    def scopeAt(point: ExpressionID): Int = points(point).scope

    /** The variables the body declares. */
    lazy val locals: Set[Identifier] = points.values
      .collect {
        case ProgramPoint(_, Let(vd, _, _), _) => vd.id
        case ProgramPoint(_, LetVar(vd, _, _), _) => vd.id
      }
      .toSet

    /** The parameters and the variables the body declares. */
    lazy val declared: Set[Identifier] = params.map(_.id).toSet ++ locals

    /** The results each point reads: those of its operands, except the one it passes on as its own. */
    lazy val dependsOn: Map[ExpressionID, Set[ExpressionID]] = points.map { case (id, point) =>
      val Deconstructor(operands, _) = point.e: @unchecked

      id -> operands.map(exitOf).filter(_ != exitOf(point.e)).toSet
    }

    /** Adds the point of `e`, at `scope`. */
    private def withProgramPoint(scope: Int, e: Expr): HeapApproximationGraph = {
      assert(!points.contains(ExpressionID(e)), s"Expression instance appears twice in the graph: $e")

      copy(points = points + (ExpressionID(e) -> ProgramPoint(scope, e)))
    }

    /** Adds an edge from `from` to `to`. */
    private def withTransition(from: ExpressionID, to: ExpressionID): HeapApproximationGraph =
      withTransitions(from, Set(to))

    /** Adds an edge from `from` to each point of `to`. */
    private def withTransitions(from: ExpressionID, to: Set[ExpressionID]): HeapApproximationGraph =
      copy(
        parents = to.foldLeft(parents)((parents, to) => parents + (to -> (parents.getOrElse(to, Set.empty) + from))),
        transitions = transitions + (from -> (transitions.getOrElse(from, Set.empty) ++ to))
      )

    /** The points with an edge to `point`. */
    def parentsOf(point: ProgramPoint): Seq[ProgramPoint] =
      parents.getOrElse(point.id, Set.empty).toSeq.map(points)

    /** The points `point` has an edge to. */
    def nextOf(point: ProgramPoint): Seq[ProgramPoint] =
      transitions.getOrElse(point.id, Set.empty).toSeq.map(points)

    /** The point whose result is the result of `e`: the body of a binding, the condition of a loop, `e` itself otherwise. */
    def exitOf(e: Expr): ExpressionID = e match {
      case Let(_, _, body) => exitOf(body)
      case LetVar(_, _, body) => exitOf(body)
      case LetRec(_, body) => exitOf(body)
      case While(cond, _, _, _, _) => exitOf(cond)

      case _ => ExpressionID(e)
    }

    /** Records at each point the variables live after it, the variables captured by a lambda or a local function being always live. */
    private def computeLiveness(using Symbols): HeapApproximationGraph = {
      def readsCollection(value: Expr): Boolean = value match {
        case _: Snapshot | _: FreshCopy => false
        case _: ArraySelect | _: MutableMapApply => true
        case _ =>
          val Deconstructor(operands, _) = value: @unchecked
          operands.exists(readsCollection)
      }

      def sourcesOf(value: Expr): Set[Identifier] =
        if (readsCollection(value)) exprOps.variablesOf(value).map(_.id) else Set.empty

      val sources: Map[Identifier, Set[Identifier]] = points.values
        .toSeq
        .flatMap(_.e match {
          case Let(vd, value, _) => Seq(vd.id -> sourcesOf(value))
          case LetVar(vd, value, _) => Seq(vd.id -> sourcesOf(value))
          case Assignment(v, value) => Seq(v.id -> sourcesOf(value))
          case ArrayUpdate(array, _, value) => exprOps.variablesOf(value).toSeq.map(_.id -> exprOps.variablesOf(array).map(_.id))
          case MutableMapUpdate(map, _, value) => exprOps.variablesOf(value).toSeq.map(_.id -> exprOps.variablesOf(map).map(_.id))
          case _ => Seq.empty
        })
        .groupMapReduce(_._1)(_._2)(_ ++ _)

      @tailrec
      def withSources(pending: List[Identifier], visited: Set[Identifier]): Set[Identifier] = pending match {
        case Nil => visited
        case head :: rest if visited(head) => withSources(rest, visited)
        case head :: rest => withSources(sources.getOrElse(head, Set.empty).toList ++ rest, visited + head)
      }

      def usesOf(e: Expr): Set[Identifier] = e match {
        case v: Variable => withSources(List(v.id), Set.empty)
        case e @ WriteBack(_) => Set(e.v.id)
        case w: While =>
          (w.pred.toSeq ++ w.pred2)
            .flatMap(exprOps.variablesOf)
            .map(_.id)
            .toSet
        case _ => Set.empty
      }

      def definedBy(e: Expr): Set[Identifier] = e match {
        case Let(vd, _, _) => Set(vd.id)
        case LetVar(vd, _, _) => Set(vd.id)
        case Assignment(v, _) => Set(v.id)
        case _ => Set.empty
      }

      def capturedBy(e: Expr): Set[Identifier] = e match {
        case lambda: Lambda => exprOps.variablesOf(lambda).map(_.id)
        case LetRec(fds, _) =>
          fds
            .flatMap(fd => exprOps.variablesOf(fd.fullBody) -- fd.params.map(_.toVariable))
            .map(_.id)
            .toSet
        case _ => Set.empty
      }

      val returned = points.values.collect { case ProgramPoint(_, LetVar(_, Variable(id, _, _), _), _) => id }.toSet

      def liveIn(id: ExpressionID, liveOut: Map[ExpressionID, Set[Identifier]]): Set[Identifier] =
        usesOf(points(id).e) ++ (liveOut.getOrElse(id, Set.empty) -- definedBy(points(id).e))

      @tailrec
      def propagate(pending: List[ExpressionID], liveOut: Map[ExpressionID, Set[Identifier]]): Map[ExpressionID, Set[Identifier]] = pending match {
        case Nil => liveOut
        case id :: rest =>
          val out =
            if (id == exitpoint) params.map(_.id).toSet -- returned
            else transitions.getOrElse(id, Set.empty).flatMap(liveIn(_, liveOut))

          if (liveOut.get(id).contains(out)) {
            return propagate(rest, liveOut)
          }

          val next = parents.getOrElse(id, Set.empty).toList ++ rest

          propagate(next, liveOut + (id -> out))
      }

      val captured = points.values
        .flatMap(point => capturedBy(point.e))
        .toSet
      val liveOut = propagate(points.keys.toList, Map.empty)

      copy(points = points.map { case (id, point) => id -> point.copy(live = liveOut.getOrElse(id, Set.empty) ++ definedBy(point.e) ++ captured) })
    }
  }

  object HeapApproximationGraph {
    /** The graph of `e`, a body with parameters `params`, whose points start at scope `baseScope`. */
    def build(params: Seq[ValDef], e: Expr, baseScope: Int = 0)(using symbols: Symbols): HeapApproximationGraph = {
      def isSingleton(e: Expr): Boolean = e.getClass.getName.endsWith("$")

      def buildRec(graph: HeapApproximationGraph, scope: Int, next: Set[ExpressionID], e: Expr): (ExpressionID, HeapApproximationGraph) = e match {
        case e @ Let(_, value, body) =>
          val newPoint = ExpressionID(e)
          val (valuePoint, graph1) = buildRec(graph, scope + 1, Set(newPoint), value)
          val (bodyPoint, graph2) = buildRec(graph1, scope + 1, next, body)

          val graph3 = graph2
            .withProgramPoint(scope + 1, e)
            .withTransition(newPoint, bodyPoint)

          (valuePoint, graph3)

        case e @ LetVar(_, value, body) =>
          val newPoint = ExpressionID(e)
          val (valuePoint, graph1) = buildRec(graph, scope + 1, Set(newPoint), value)
          val (bodyPoint, graph2) = buildRec(graph1, scope + 1, next, body)

          val graph3 = graph2
            .withProgramPoint(scope + 1, e)
            .withTransition(newPoint, bodyPoint)

          (valuePoint, graph3)

        case e @ LetRec(_, body) =>
          val newPoint = ExpressionID(e)
          val (bodyPoint, graph1) = buildRec(graph, scope, next, body)

          val graph2 = graph1
            .withProgramPoint(scope, e)
            .withTransition(newPoint, bodyPoint)

          (newPoint, graph2)

        case e @ Assignment(_, value) =>
          val newPoint = ExpressionID(e)
          val (valuePoint, graph1) = buildRec(graph, scope, Set(newPoint), value)

          val graph2 = graph1
            .withProgramPoint(scope, e)
            .withTransitions(newPoint, next)

          (valuePoint, graph2)

        case e @ FieldAssignment(obj, _, value) =>
          val newPoint = ExpressionID(e)
          val (valuePoint, graph1) = buildRec(graph, scope, Set(newPoint), value)
          val (objPoint, graph2) = buildRec(graph1, scope, Set(valuePoint), obj)

          val graph3 = graph2
            .withProgramPoint(scope, e)
            .withTransitions(newPoint, next)

          (objPoint, graph3)

        case e @ ArrayUpdate(array, index, value) =>
          val newPoint = ExpressionID(e)
          val (valuePoint, graph1) = buildRec(graph, scope, Set(newPoint), value)
          val (indexPoint, graph2) = buildRec(graph1, scope, Set(valuePoint), index)
          val (arrayPoint, graph3) = buildRec(graph2, scope, Set(indexPoint), array)

          val graph4 = graph3
            .withProgramPoint(scope, e)
            .withTransitions(newPoint, next)

          (arrayPoint, graph4)

        case e @ MutableMapUpdate(map, key, value) =>
          val newPoint = ExpressionID(e)
          val (valuePoint, graph1) = buildRec(graph, scope, Set(newPoint), value)
          val (keyPoint, graph2) = buildRec(graph1, scope, Set(valuePoint), key)
          val (mapPoint, graph3) = buildRec(graph2, scope, Set(keyPoint), map)

          val graph4 = graph3
            .withProgramPoint(scope, e)
            .withTransitions(newPoint, next)

          (mapPoint, graph4)

        case e @ IfExpr(cond, thn, els) =>
          val newPoint = ExpressionID(e)
          val (thnPoint, graph1) = buildRec(graph, scope + 1, Set(newPoint), thn)
          val (elsPoint, graph2) = buildRec(graph1, scope + 1, Set(newPoint), els)
          val (condPoint, graph3) = buildRec(graph2, scope, Set(thnPoint, elsPoint), cond)

          val graph4 = graph3
            .withProgramPoint(scope, e)
            .withTransitions(newPoint, next)

          (condPoint, graph4)

        case e: MatchExpr if !symbols.containsMutableType(e) =>
          val newPoint = ExpressionID(e)
          val graph1 = graph
            .withProgramPoint(scope, e)
            .withTransitions(newPoint, next)

          (newPoint, graph1)

        case e: MatchExpr =>
          throw AliasingRewriteException.unsupportedConstruct(e)

        case e: Lambda =>
          val newPoint = ExpressionID(e)
          val graph1 = graph
            .withProgramPoint(scope, e)
            .withTransitions(newPoint, next)

          (newPoint, graph1)

        case e @ While(cond, body, _, _, _) =>
          val newPoint = ExpressionID(e)
          val (bodyPoint, graph1) = buildRec(graph, scope + 1, Set(newPoint), body)
          val (condPoint, graph2) = buildRec(graph1, scope, Set(bodyPoint) ++ next, cond)

          val graph3 = graph2
            .withProgramPoint(scope, e)
            .withTransition(newPoint, condPoint)

          (newPoint, graph3)

        case e @ Return(body) =>
          val newPoint = ExpressionID(e)
          val (bodyPoint, graph1) = buildRec(graph, scope, Set(newPoint), body)

          val graph2 = graph1
            .withProgramPoint(scope, e)
            .withTransition(newPoint, graph1.exitpoint)

          (bodyPoint, graph2)

        case e: Error =>
          val newPoint = ExpressionID(e)
          val graph1 = graph.withProgramPoint(scope, e)

          (newPoint, graph1)

        case e @ Block(exprs, last) =>
          val newPoint = ExpressionID(e)
          val graph1 = graph
            .withProgramPoint(scope, e)
            .withTransitions(newPoint, next)

          (exprs :+ last).foldRight((newPoint, graph1)) { case (child, (next, graph)) =>
            buildRec(graph, scope + 1, Set(next), child)
          }

        case other =>
          val Deconstructor(operands, _) = other: @unchecked
          val expressions = operands.filterNot(isSingleton)
          val newPoint = ExpressionID(other)
          val graph1 = graph
            .withProgramPoint(scope, other)
            .withTransitions(newPoint, next)

          if (expressions.isEmpty) {
            return (newPoint, graph1)
          }

          expressions.foldRight((newPoint, graph1)) { case (child, (next, graph)) =>
            buildRec(graph, scope, Set(next), child)
          }
      }

      val entryLiteral = UnitLiteral()
      val exitLiteral = UnitLiteral()
      val entrypoint = ExpressionID(entryLiteral)
      val exitpoint = ExpressionID(exitLiteral)

      val initialGraph = HeapApproximationGraph(params, entrypoint, exitpoint, Map.empty, Map.empty, Map.empty)
        .withProgramPoint(baseScope, exitLiteral)

      val (bodyEntrypoint, graph) = buildRec(initialGraph, baseScope + 1, Set(exitpoint), e)

      graph
        .withProgramPoint(baseScope, entryLiteral)
        .withTransition(entrypoint, bodyEntrypoint)
        .computeLiveness
    }
  }
}
