/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package utils

import extraction.xlang.{ trees => xt }

import scala.collection.mutable.{ Map => MutableMap, Set => MutableSet }

/**
 * Keep track of the valid data (functions & classes) as they come, in a thread-safe fashion.
 *
 * Call [[update]] ([[remove]]) whenever new data is (no longer) available, and [[checkpoints]]
 * when all the data is available. New data can then be added through [[update]] calls and,
 * again, a [[checkpoints]] call. Every one of these calls yields a collection of [[xt.Symbols]]
 * that are self-contained programs, ready to be further processed.
 *
 * During the first [[update]]/[[remove]] - [[checkpoints]] cycle, the graph is updated as data
 * arrives. During the next cycles, the graph is frozen until the [[checkpoints]] to allow
 * inconsistent state in the graph to not impact the computation.
 * TODO maybe [[freeze]]/[[unfreeze]] should be exposed and let the user manage this.
 *
 * Specific implementation of this trait have to provide a context and facilities to compute
 * direct dependencies for functions and classes, as well as filters to identify data that
 * identify data that is of interest.
 */
trait Registry {

  /******************* Public Interface ***********************************************************/

  /**
   * Update the graph with the new/updated classes and functions.
   *
   * With the new information, if something is ready to be verified, [[update]] returns
   * sequences of self-contained symbols required for verification.
   *
   * NOTE distinguish sealed and non-sealed class hierarchies. Handle the latter appropriately.
   *      To do that, we can:
   *       - delay the insertion of classes in the graph,
   *       - once notified that everything was compiled, consider all classes as sealed,
   *         and insert them all in the graph as usual (see [[checkpoints]]).
   * FIXME However, this adds a BIG assumption on the runtime: no new class should be available!
   *       So, maybe we just don't want that???
   */
  def update(classes: Seq[xt.ClassDef], functions: Seq[xt.FunDef]): Option[xt.Symbols] = {
    def isReady(cd: xt.ClassDef): Boolean = getTopLevels(classes, cd) match {
      case Some(tops) if tops.isEmpty =>
        (cd.flags contains xt.IsSealed) || // Explicitly sealed is good.
        !(cd.flags contains xt.IsAbstract) // Because we do not allow inheriting from case classes.
      case Some(tops) =>
        tops forall { top => top.flags contains xt.IsSealed } // All parents must be sealed.
      case None =>
        false // Some parents are in different compilation unit, hence not ready.
    }

    val (ready, open) = classes partition isReady
    this.synchronized {
      knownClasses ++= open map { cd => cd.id -> cd }
    }

    classes foreach { cd =>
      if ((cd.flags contains xt.IsAbstract) && !(cd.flags contains xt.IsSealed))
        ctx.reporter.warning(cd.getPos, s"Consider sealing ${cd.id}.")
    }

    process(ready, functions)
  }

  /**
   * Remove from the registry and underlying graph the given classes and functions.
   */
  def remove(classes: Seq[xt.ClassDef], functions: Seq[xt.FunDef]): Unit = {
    val classIds = classes map { _.id }
    val funIds = functions map { _.id }
    knownClasses --= classIds
    (classIds ++ funIds) foreach graph.remove
  }

  /**
   * To be called once every compilation unit were extracted.
   */
  def checkpoints(): Option[xt.Symbols] = {
    val defaultRes = process(knownClasses.values.toSeq, Seq.empty)
    val res = if (frozen) {
      assert(defaultRes.isEmpty)
      graph.unfreeze() map { case (cls, funs) => xt.NoSymbols.withClasses(cls.toSeq).withFunctions(funs.toSeq) }
    } else {
      frozen = true
      defaultRes
    }

    graph.freeze() // (re-)freeze for next cycle
    res
  }


  /******************* Customisation Points *******************************************************/

  protected val ctx: inox.Context

  /** Compute the set of direct, non-recursive dependencies of the given [[xt.FunDef]] or [[xt.ClassDef]]. */
  protected def computeDirectDependencies(fd: xt.FunDef): Set[Identifier]
  protected def computeDirectDependencies(cd: xt.ClassDef): Set[Identifier]

  /** Checks whether the given function/class should be verified at some point. */
  protected def shouldBeChecked(fd: xt.FunDef): Boolean
  protected def shouldBeChecked(cd: xt.ClassDef): Boolean


  /******************* Implementation: Dependency Graph *******************************************/

  private type NodeValue = Either[xt.ClassDef, xt.FunDef] // "Union" type.

  private type Result = (Set[xt.ClassDef], Set[xt.FunDef])
  private val EmptyResult = (Set[xt.ClassDef](), Set[xt.FunDef]())

  private val knownClasses = MutableMap[Identifier, xt.ClassDef]()

  private var frozen = false
  private val graph = new IncrementalComputationalGraph[Identifier, NodeValue, Result] {
    override def compute(ready: Set[(Identifier, NodeValue)]): Result = {
      (EmptyResult /: ready) { case ((cls, funs), (_, node)) =>
        node match {
          case Left(cd) => (cls + cd, funs)
          case Right(fd) => (cls, funs + fd)
        }
      }
    }

    private val cfCache = MutableMap[Identifier, CanonicalForm]()

    override def equivalent(id: Identifier, deps: Set[Identifier],
                            oldInput: NodeValue, newInput: NodeValue): Boolean = {
      val (cf1, cf2) = (oldInput, newInput) match {
        case (Left(cd1), Left(cd2)) =>
          val cf1 = cfCache.getOrElseUpdate(id, CanonicalFormBuilder(cd1))
          val cf2 = CanonicalFormBuilder(cd2)
          (cf1, cf2)

        case (Right(fd1), Right(fd2)) =>
          val cf1 = cfCache.getOrElseUpdate(id, CanonicalFormBuilder(fd1))
          val cf2 = CanonicalFormBuilder(fd2)
          (cf1, cf2)

        case _ => ctx.reporter.fatalError(s"Unexpected type mismatch for $id")
      }

      if (cf1 == cf2) true
      else {
        cfCache += id -> cf2
        false
      }
    }
  }

  private def isOfInterest(node: NodeValue): Boolean = node match {
    case Left(cd) => shouldBeChecked(cd)
    case Right(fd) => shouldBeChecked(fd)
  }

  private def process(classes: Seq[xt.ClassDef], functions: Seq[xt.FunDef]): Option[xt.Symbols] = {
    // Compute direct dependencies and insert the new information into our dependency graph
    val clusters = computeClusters(classes)
    val invariants = computeInvariantMapping(functions)
    def computeAllDirectDependencies(cd: xt.ClassDef) =
      computeDirectDependencies(cd) ++ clusters(cd) ++ invariants(cd)

    val newNodes: Seq[(Identifier, NodeValue, Set[Identifier])] =
      (classes map { cd => (cd.id, Left(cd): NodeValue, computeAllDirectDependencies(cd)) }) ++
      (functions map { fd => (fd.id, Right(fd): NodeValue, computeDirectDependencies(fd)) })

    // Critical Section
    val results: Seq[Result] =
      this.synchronized {
        newNodes flatMap { case (id, input, deps) => graph.update(id, input, deps, isOfInterest(input)) }
      }

    if (results.isEmpty) None
    else {
      // Group into one set of Symbols to avoid verifying the same things several times
      // TODO this is just because we don't have caching later on in the pipeline (YET).
      // Also, it doesn't work 100% of the time.
      val (clsSets, funsSets) = results.unzip
      val cls = (Set[xt.ClassDef]() /: clsSets) { _ union _ }
      val funs = (Set[xt.FunDef]() /: funsSets) { _ union _ }
      Some(xt.NoSymbols.withClasses(cls.toSeq).withFunctions(funs.toSeq))
    }
  }


  /******************* Implementation: Class Hierarchy ********************************************/

  /**
   * We create "clusters" for classes:
   * they define class hierarchies based on the given subset of all classes.
   *
   * It is expected that for each class in [[classes]], all its parents are also
   * contained in [[classes]].
   *
   * The returned mapping is total, i.e. every given class yield a (possibly empty) Set.
   *
   * For example:
   *   trait A; trait B; trait E
   *   class C extends A with B
   *   class D extends B
   *   class F extends E
   *   class G extends F
   * gives the mapping
   *   A -> { C }
   *   B -> { C, D }
   *   C -> { A, B }
   *   D -> { B }
   *   E -> { F, G }
   *   F -> { E }
   *   G -> { E }
   * which means that, by transitivity, G and F depend on each others.
   */
  private type ClusterMap = Map[xt.ClassDef, Set[Identifier]]
  private def computeClusters(classes: Seq[xt.ClassDef]): ClusterMap = {
    // Build two mappings:
    //  - from top level parents to children, and
    //  - from children to top level parents.
    val toplevels = MutableMap[xt.ClassDef, MutableSet[Identifier]]()
    val reverse   = MutableMap[xt.ClassDef, MutableSet[Identifier]]()

    classes foreach { cd =>
      val tops = forceGetTopLevels(classes, cd)
      tops foreach { top => toplevels.getOrElseUpdate(top, MutableSet.empty) += cd.id }
      reverse.getOrElseUpdate(cd, MutableSet.empty) ++= tops map { _.id }
    }

    // Combine the two mappings.
    val mapping = MutableMap[xt.ClassDef, Set[Identifier]]()
    classes foreach { cd =>
      val deps = Set.empty ++ toplevels.getOrElse(cd, Set.empty) ++ reverse(cd) - cd.id
      mapping += cd -> deps
    }

    mapping.toMap
  }

  /**
   * Find the top level parents for the given class, returns empty seq when no inheritance.
   *
   * Return None if a dependency is not known.
   */
  private def getTopLevels(classes: Seq[xt.ClassDef], cd: xt.ClassDef): Option[Set[xt.ClassDef]] = try {
    Some(getTopLevelsImpl(classes, cd))
  } catch {
    case IncompleteHierarchy(_, _, _) => None
  }

  /** Same as [[getTopLevels]], but assuming that all dependencies are known. */
  private def forceGetTopLevels(classes: Seq[xt.ClassDef], cd: xt.ClassDef): Set[xt.ClassDef] = try {
    getTopLevelsImpl(classes, cd)
  } catch {
    case IncompleteHierarchy(id, parent, universe) =>
      ctx.reporter.internalError(s"Couldn't find parent $parent of $id in <${universe map { _.id } mkString ", "}>")
  }


  case class IncompleteHierarchy(cd: Identifier, parent: Identifier, classes: Seq[xt.ClassDef]) extends Throwable
  private def getTopLevelsImpl(classes: Seq[xt.ClassDef], cd0: xt.ClassDef): Set[xt.ClassDef] = {
    def getDirects(cd: xt.ClassDef): Set[xt.ClassDef] = cd.parents.toSet map { ct: xt.ClassType =>
      classes find { _.id == ct.id } getOrElse { throw IncompleteHierarchy(cd.id, ct.id, classes) }
    }

    if (cd0.parents.isEmpty) Set.empty
    else getDirects(cd0) flatMap { p => if (p.parents.isEmpty) Set(p) else getTopLevelsImpl(classes, p) }
  }


  /******************* Implementation: Class Invariant ********************************************/

  /**
   * Compute a (total) mapping, solely based on the given [[functions]], to identify
   * class dependency toward the function that represent their invariant, if any.
   */
  private type InvariantMapping = xt.ClassDef => Option[Identifier]
  private def computeInvariantMapping(functions: Seq[xt.FunDef]): InvariantMapping = {
    // Build a database (class id -> invariant id mapping) by extracting
    // information from functions' flags:
    //  - keep only invariants;
    //  - identify the class it belongs to;
    //  - project the function unto its id;
    //  - group info by class id;
    //  - ensures that at most one invariant is defined by class.
    val db: Map[Identifier, Option[Identifier]] =
      functions collect {
        case fd if fd.flags contains xt.IsInvariant =>
          val cid = fd.flags collectFirst { case xt.IsMethodOf(id) => id } getOrElse {
            ctx.reporter.internalError(s"Expected to find a IsMethodOf flag for invariant function ${fd.id}")
          }

          cid -> fd.id
      } groupBy {
        case (cid, fid) => cid
      } map { case (cid, xs) =>
        val fids = xs map { _._2 } // Map cid -> Seq[fid]
        if (fids.size != 1) {
          ctx.reporter.internalError(s"Expected to find one invariant for class $cid, got <${fids mkString ", "} >.")
        }

        cid -> Some(fids.head)
      }

    (cd: xt.ClassDef) => { db.getOrElse(cd.id, None) }
  }

}

