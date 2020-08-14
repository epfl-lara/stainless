/* Copyright 2009-2020 EPFL, Lausanne */

package stainless
package extraction
package imperative

import scala.collection.mutable.{HashMap => MutableMap}

trait AliasAnalyzer extends oo.CachingPhase {
  val s: Trees
  val t: s.type

  import s._
  import exprOps._

  protected type TransformerContext <: AliasAnalysis

  trait AliasAnalysis { self: TransformerContext =>
    implicit val symbols: s.Symbols
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

  case class Summaries(functions: Map[FunDef, Summary])

  object Summaries {
    val empty = Summaries(Map.empty)
  }

  // For every parameter, we approximate whether, and if so, where the original object was captured
  case class Summary(captures: Map[ValDef, Set[ValDef]])

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

  // The target of a reference, i.e, the object pointed to depending on the path condition
  // Generally, Targets found in the core data structures (such as Graph) should always partition
  // the state space, i.e., `\/_i cond_i = true` and `forall i,j. cond_i /\ cond_j = false`.
  // However, this invariant may be broken for targets produced by intermediate operations.
  case class Target(pairs: Seq[(Expr, Object)]) {
    def toSeq: Seq[(Expr, Object)] = pairs
    def objects: Seq[Object] = pairs.map(_._2)

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
    containers: Map[Object, Target], // back edges for contents  // FIXME, doesn't make sense atm
    bindings: Map[ValDef, Target], // mapping from program bindings to heap objects
    escaped: Set[Object], // objects that escaped and thus don't have precise information about
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
          this.contents(obj).values.flatMap(_.objects.toSet)
        }
      })(initialObjects)
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

  // Graph computation

  private[imperative] def computeGraph(inputs: Seq[ValDef], expr: Expr)(
    implicit ctx: inox.Context, symbols: Symbols): (Graph, Option[BindingTarget]) =
  {
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
    def havoc(g: Graph, targets: Seq[Target]): Graph = {
      // TODO: Cut down the initialObjects set by using the path condition
      val initialObjects = targets.flatMap(target => target.objects)
      val reachableObjects = g.computeReachable(initialObjects.toSet)
      g.havoc(reachableObjects)
    }

    // Mark all objects reachable from the given targets as escaped
    def escape(g: Graph, targets: Seq[Target]): Graph = {
      // TODO: Cut down the initialObjects set by using the path condition
      val initialObjects = targets.flatMap(target => target.objects)
      val reachableObjects = g.computeReachable(initialObjects.toSet)
      g.withEscaped(reachableObjects)
    }

    def rec(g: Graph, expr: Expr): (Graph, Option[Target]) = {
      def recSequential(g: Graph, exprs: Seq[Expr]): (Graph, Seq[Option[Target]]) =
        exprs.foldLeft((g, Seq.empty[Option[Target]])) { case ((ga, targets), expr) =>
          val (gb, target) = rec(ga, expr)
          (gb, target +: targets)
        }

      expr match {
        case v: Variable =>
          val targetOpt = g.bindings.get(v.toVal)
          assert(!isHeapType(v.tpe) || targetOpt.isDefined)

          val escapedTargetObjs = g.escaped intersect targetOpt.get.objects.toSet
          if (escapedTargetObjs.nonEmpty) {
            val objsStr = escapedTargetObjs.mkString("{", ", ", "}")
            ctx.reporter.fatalError(s"Invalid program: reference to escaped objects $objsStr")
          }

          (g, targetOpt)

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
          val accessor = Accessor(field)
          if (accessor.yieldsHeapTypeOn(recv.getType)) {
            val (g1, recvTarget) = prepareForAccess(g, recv, accessor)
            val (g2, Some(valueTarget)) = rec(g1, value)
            val g3 = update(g2, recvTarget, accessor, valueTarget)
            (g3, None) // returns Unit, so no heap object
          } else {
            (g, None)
          }

        // case fi: FunctionInvocation if !symbols.isRecursive(fi.id) =>
        //   exprOps.withoutSpecs(symbols.simplifyLets(fi.inlined))
        //     .map(rec(g, _))
        //     .getOrElse(???)

        case fi: FunctionInvocation =>
          val fd = fi.tfd.fd

          val (g1, argTargets) = recSequential(g, fi.args)

          val escParams = getEscapingParams(fd)
          val (escTargets_, nonEscTargets_) = fd.params
            .zip(argTargets)
            .partition { case (p, _) => escParams.contains(p) }
          val escTargets = escTargets_.collect { case (p, Some(t)) => t }
          val nonEscTargets = nonEscTargets_.collect { case (p, Some(t)) => t }

          // Havoc non-escaping targets
          val g2 = havoc(g1, nonEscTargets)

          // Havoc and mark escaping arguments
          val g3 = escape(g2, escTargets)

          // Add new object returned from the call
          val returnTpe = fi.getType
          val (g4, targetOpt) = if (isHeapType(returnTpe)) {
            val returnObj = Object.fresh("ret", returnTpe)
            (g3.withObject(returnObj), Some(Target(returnObj)))
          } else {
            (g3, None)
          }

          (g4, targetOpt)

        case _ =>
          val kind = expr.getClass.getName
          ctx.reporter.fatalError(s"Unsupported expr of kind $kind: $expr")
      }
    }

    // Create the initial graph containing only the inputs
    val inputObjects = inputs.filter(isHeapParam).map(input => Object(input.freshen))
    val contents = inputObjects.map(_ -> Map.empty[Accessor, Target]).toMap
    val bindings = inputs.zip(inputObjects.map(Target.apply)).toMap
    val graph = Graph(inputObjects.toSet, contents, Map.empty, bindings, Set.empty)

    val (resultGraph, resultTargetOpt) = rec(graph, expr)
    (resultGraph, resultTargetOpt.map(target => (ValDef(ResultId, expr.getType), target)))
  }

  private[imperative] def dumpGraph(graph: Graph, resultOpt: Option[BindingTarget], path: String,
      showContainers: Boolean = false)(implicit ctx: inox.Context): Unit =
  {
    import java.nio.file.{Files, Paths}

    // println(s" --- Function ${fd.id}: ---")
    // println(s"OBJECTS: ${graph.objects}")
    // println(s"CONTENTS: ${graph.contents}")

    // Describe graph in DOT syntax
    def I(id: Identifier) = id.uniqueName.toString.replace('$', '_').replace(".", "__")
    def N(id: Identifier) = id.toString
    def trim(s: String, maxLength: Int = 20) =
      if (s.length > maxLength) s.slice(0, maxLength-3) + "..." else s

    def describeTarget(src: String, target: Target, opts: Seq[String] = Seq.empty): String = {
      target.toSeq.map { case (cond, recv) =>
        val lblOpts = if (cond == True) Seq.empty
          else Seq(s"""taillabel="${trim(cond.toString)}"""", "labelfontsize=10")
        val allOpts = lblOpts ++ opts
        s"""$src -> obj_${I(recv.vd.id)} [${allOpts.mkString(", ")}]"""
      } .mkString("\n")
    }

    val objects = graph.objects.map { obj =>
      // Object name and record fields
      val fields = graph.contents(obj)
      val fieldsStr = if (fields.nonEmpty) {
        fields.keys.toSeq.sortBy(_.id).map(f => s"<${I(f.id)}> ${N(f.id)}").mkString("|")
      } else ""
      val lbl = s"""label="{${N(obj.vd.id)} | {$fieldsStr}}""""

      // Mark escaped objects
      val escapedOpt = if (graph.escaped.contains(obj)) Some("color=crimson") else None

      val allOpts = Seq(lbl) ++ escapedOpt
      s"""obj_${I(obj.vd.id)}[${allOpts.mkString(", ")}]"""
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
      s"""bdg_${I(bdg.id)}[label="${N(bdg.id)}", style="bold,rounded"]"""
    }
    val bindingEdges = bindingsAndResult.map { case (bdg, target) =>
      describeTarget(s"bdg_${I(bdg.id)}", target, Seq("style=bold"))
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
