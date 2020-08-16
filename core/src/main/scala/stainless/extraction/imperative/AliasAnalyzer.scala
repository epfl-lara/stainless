/* Copyright 2009-2020 EPFL, Lausanne */

package stainless
package extraction
package imperative

import scala.collection.mutable.{HashSet => MutableSet}
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

      // FIXME: There seems to be a bug in DiGraph#stronglyConnnectedComponents that omits nodes
      val res = symbols.sccs.topSort.reverse.foldLeft(Summaries.empty) { case (summaries, scc) =>
        val fds = scc.map(symbols.getFunction(_))
        val emptySummariesForScc = Summaries(fds.map(_ -> Summary(Map.empty)).toMap)
        var iteration = 0
        inox.utils.fixpoint[Summaries] { summaries =>
          iteration += 1
          fds.foldLeft(summaries)(updateStep(_, _, iteration))
        } (summaries merge emptySummariesForScc)
      }

      println(s"\n=== SUMMARIES ===\n${res.asString}\n")
      res
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

  // A field accessor (only class fields for now)
  case class Accessor(id: Identifier) {
    // Returns the class field on the given type, if any
    def fieldOn(recvTpe: Type)(implicit symbols: Symbols): Option[ValDef] =
      recvTpe match {
        case ct: ClassType => symbols.getClassField(ct, id)
        case _ => None
      }

    def yieldsHeapTypeOn(recvTpe: Type)(implicit symbols: Symbols): Boolean =
      fieldOn(recvTpe).map(f => isHeapType(f.tpe)).getOrElse(false)
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
        case BooleanLiteral(false) => Target(Seq.empty)
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
  }

  object Target {
    def apply(obj: Object): Target = Target(Seq((True, obj)))
  }

  // A graph representing a heap state and bindings into it symbolically
  case class Graph(
    objects: Set[Object],
    contents: Map[Object, Map[Accessor, Target]],
    blockedBy: Map[Object, Set[Object]], // for a captured object, its potential captors
    containers: Map[Object, Target], // back edges for contents  // FIXME, doesn't make sense atm
    bindings: Map[ValDef, Target], // mapping from program bindings to heap objects
    escaped: Set[Object], // objects that escaped and we thus must give up access to
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

    def havoc(objs: Set[Object]): Graph = {
      assert(objs.subsetOf(this.objects))
      val newContents = contents ++ objs.map(_ -> Map.empty[Accessor, Target])
      this.copy(contents = newContents)
    }

    def withEscaped(objs: Set[Object]): Graph =
      havoc(objs).copy(escaped = escaped ++ objs)

    def isBindingInvalid(bdg: ValDef): Boolean =
      bindings(bdg).objects.exists(escaped)

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
        val newObj = Object.freshForAccessor(recvObj, accessor)
        newObjects = newObjects + newObj
        newContents = newContents + (newObj -> Map.empty)
        newContents = Graph.updatedContents(newContents, recvObj, accessor, Target(newObj))
      }
      this.copy(objects = newObjects, contents = newContents)
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
    def prepareForAccess(g: Graph, recv: Expr, accessor: Accessor): (Graph, Target) = {
      val (g1, Some(recvTarget)) = rec(g, recv)
      val g2 = g1.ensureObjectsUnfoldedAt(recvTarget.objects, accessor)
      (g2, recvTarget)
    }

    // Computes the new contents on objects assuming we update `accessor` on `recvTargets`
    // TODO: Try to eliminate targets using the path condition and a simplifier or solver?
    def update(g: Graph, recvTarget: Target, accessor: Accessor, valueTarget: Target): Graph =
    {
      // Gather the conditions under which a receiver object will be modified
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

    // Erase all information about objects reachable from the given object
    def havoc(g: Graph, targets: Seq[Target]): Graph =
      g.havoc(g.computeReachable(targets))

    // Mark all objects reachable from the given targets as escaped
    def escape(g: Graph, targets: Seq[Target]): Graph =
      g.withEscaped(g.computeReachable(targets))

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

        // Mark all the proper subobjects of `obj` as escaped
        val subObjs = g.computeReachable(captives)
        val g1 = g.havoc(subObjs).copy(escaped = g.escaped ++ (subObjs diff captives))

        // Record who captured what, so we can perhaps release the captives later
        assert((g1.blockedBy.keySet intersect captives).isEmpty)
        g1.copy(blockedBy = g1.blockedBy ++ captives.map(_ -> captors))
      }

    // Release the underlying objects by making its captors escape
    def ensureReleased(g: Graph, target: Target): Graph = {
      val captives = g.computeReachable(target.objectSet) intersect g.blockedBy.keySet
      if (captives.nonEmpty) {
        val captors = captives.flatMap(g.blockedBy)
        g.withEscaped(g.computeReachable(captors))
      } else {
        g
      }
    }

    def rec(g: Graph, expr: Expr): (Graph, Option[Target]) = {
      def recSequential(g: Graph, exprs: Seq[Expr]): (Graph, Seq[Option[Target]]) =
        exprs.foldLeft((g, Seq.empty[Option[Target]])) { case ((ga, targets), expr) =>
          val (gb, target) = rec(ga, expr)
          (gb, target +: targets)
        }

      expr match {
        case v: Variable =>
          g.bindings.get(v.toVal) match {
            case targetOpt @ Some(target) =>
              val escapedTargetObjs = g.escaped intersect g.computeReachable(target.objectSet)
              if (escapedTargetObjs.nonEmpty) {
                val objsStr = escapedTargetObjs.mkString(", ")
                ctx.reporter.fatalError(v.getPos, s"Reference to escaped objects {$objsStr}")
              }

              val g1 = ensureReleased(g, target)
              (g1, Some(target))
            case None =>
              assert(!isHeapType(v.tpe))
              (g, None)
          }

        case Let(vd, value, body) =>
          val (g1, valueTargetOpt) = rec(g, value)
          val g2 = valueTargetOpt.map(g1.withBinding(vd, _)).getOrElse(g1)
          rec(g2, body)

        case Block(exprs, lastExpr) =>
          val g1 = exprs.foldLeft(g) { case (g, expr) => rec(g, expr)._1 }
          rec(g1, lastExpr)

        case _: Literal[_] =>
          // Literals are not heap objects
          (g, None)

        case ClassConstructor(ct, args) =>
          val obj = Object.fresh("fresh", ct)
          (g.withObject(obj), Some(Target(obj)))

        case ClassSelector(recv, field) =>
          val accessor = Accessor(field)
          if (accessor.yieldsHeapTypeOn(recv.getType)) {
            val (g1, recvTarget) = prepareForAccess(g, recv, accessor)
            val accTarget = recvTarget.flatMap(g1.contents(_)(accessor))
            (g1, Some(accTarget))
          } else {
            (g, None)
          }

        case FieldAssignment(recv, field, value) =>
          // FIXME: Prevent introduction of cycles?
          val accessor = Accessor(field)
          if (accessor.yieldsHeapTypeOn(recv.getType)) {
            val (g1, recvTarget) = prepareForAccess(g, recv, accessor)
            val (g2, Some(valueTarget)) = rec(g1, value)
            val g3 = update(g2, recvTarget, accessor, valueTarget)
            (g3, None) // returns Unit, so no heap object
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

          // Add new object returned from the call
          val returnTpe = fi.getType
          val (g2, resTargetOpt) = if (isHeapType(returnTpe)) {
            val returnObj = Object.fresh("ret", returnTpe)
            (g1.withObject(returnObj), Some(Target(returnObj)))
          } else {
            (g1, None)
          }

          val paramsAndArgTargets = fd.params.zip(argTargets)
          val (captTargets, uncaptTargets) = paramsAndArgTargets
            .collect { case (p, t) if isHeapParam(p) => (p, t.get) }
            .partition { case (p, _) => calleeSummary.capturedBy.contains(p) }

          // Havoc non-escaping targets
          // TODO: Don't havoc pure parameters
          val g3 = havoc(g2, uncaptTargets.map(_._2))

          // Havoc and mark escaping arguments
          val argTargetsMap: Map[ValDef, Option[Target]] = (
              paramsAndArgTargets ++
              resTargetOpt.map(resTarget => (ValDef(ResultId, returnTpe), Some(resTarget))).toSeq
            ).toMap
          val captures = captTargets.toSeq.map { case (param, argTarget) =>
            (calleeSummary.capturedBy(param).toSeq.flatMap(argTargetsMap.apply), argTarget)
          }
          val g4 = capture(g3, captures)

          (g4, resTargetOpt)

        case _ =>
          val kind = expr.getClass.getName
          ctx.reporter.fatalError(s"Unsupported expr of kind $kind: $expr")
      }
    }

    val inputs = fd.params
    val body = exprOps.withoutSpecs(fd.fullBody).getOrElse(???)

    // Create the initial graph containing only the inputs
    val inputObjects = inputs.filter(isHeapParam).map(input => Object(input.freshen))
    val contents = inputObjects.map(_ -> Map.empty[Accessor, Target]).toMap
    val bindings = inputs.zip(inputObjects.map(Target.apply)).toMap
    val graph = Graph(inputObjects.toSet, contents, Map.empty, Map.empty, bindings, Set.empty)

    // Compute the graph at the end of the function
    val (resultGraph, resultTargetOpt) = rec(graph, body)
    val resultOpt = resultTargetOpt.map(target => (ValDef(ResultId, body.getType), target))

    // Dump the graph to dot
    dumpPath.foreach(dumpGraph(resultGraph, resultOpt, _))

    // Compute the captures
    // TODO: Do this more efficiently by walking up back edges of bindings' objects
    val capturedBy: Map[ValDef, MutableSet[ValDef]] =
      graph.bindings.keys.map(_ -> MutableSet.empty[ValDef]).toMap
    val paramBindings = fd.params.map(p => p -> resultGraph.bindings(p))
    (paramBindings ++ resultOpt).foreach { case (captorBdg, captorBdgTarget) =>
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
    val capturedByFrozen = capturedBy
      .filter { case (_, mset) => mset.nonEmpty }
      .mapValues(_.toSet)

    Summary(capturedByFrozen)
  }

  private[this] def dumpGraph(graph: Graph, resultOpt: Option[BindingTarget], path: String,
      showContainers: Boolean = false): Unit =
  {
    import java.nio.file.{Files, Paths}

    def isBindingInvalid(bdg: ValDef) =
      resultOpt match {
        case Some((resVd, _)) if resVd eq bdg => false
        case _ => graph.isBindingInvalid(bdg)
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
      val allOpts = opts ++ redOpt(isBindingInvalid(bdg))
      s"""bdg_${I(bdg.id)} ${O(allOpts)}"""
    }
    val bindingEdges = bindingsAndResult.map { case (bdg, target) =>
      val opts = Seq("style=bold") ++ redOpt(isBindingInvalid(bdg))
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
