/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package utils

import extraction.xlang.{ trees => xt }

import scala.collection.mutable.{ Map => MutableMap, Set => MutableSet, ListBuffer }

import java.io.{ File, FileInputStream, FileOutputStream, IOException }

object DebugSectionRegistry extends inox.DebugSection("registry")

/**
 * Keep track of the valid data (functions & classes) as they come, in a thread-safe fashion.
 *
 * Call [[update]] whenever new data is newly available, updated or simply still valid,
 * and [[checkpoint]] when all the data is available. New data can then be added through
 * [[update]] calls and, again, a [[checkpoint]] call. Every one of these calls yields a
 * collection of [[xt.Symbols]] that are self-contained programs, ready to be further processed.
 *
 * During the first [[update]] - [[checkpoint]] cycle, the graph is updated as data
 * arrives. During the next cycles, the graph is frozen until the [[checkpoint]] to allow
 * inconsistent state in the graph to not impact the computation. The graph is immediately
 * frozen after each [[checkpoint]], meaning one needs not explicitly freeze the graph after
 * the first cycle.
 *
 * Specific implementations of this trait have to provide a context and facilities to compute
 * direct dependencies for functions and classes, as well as filters to identify data that
 * is of interest.
 *
 * Regarding the persistent cache:
 *  - Its main purpose is to store on disk the state of the Registry, enabling the user to recover
 *    their previous verification "session" quickly. Its effect is to filter out any functions that
 *    was already processed/verified and wasn't updated since the cache was written to disk. Note
 *    that this cache doesn't take into account the status of verification (or any other component).
 *  - The cache is loaded and used for one update/checkpoint cycle, after which it is thrown away.
 *  - The cache is written to disk when asked to, i.e. when calling [[saveCache]].
 *  - It is expected that the cache is loaded before the first cycle starts. The behaviour is undefined
 *    if it is loaded during any cycle or between two cycles.
 *  - In order to re-compute nodes whose dependencies have changed, we need the knowledge of the
 *    full universe, i.e. all function and class definitions, in order to known which nodes should
 *    be (re)computed by the underlying ICG. To do that, when the cache is loaded, the [[update]] and
 *    [[checkpoint]] method will switch to a specific mode which defer all updates to [[checkpoint]].
 *  - The [[isOfInterest]] method is also switching mode whenever the persistent cache is loaded.
 *
 * NOTE If stainless is interrupted, the cache will most probably be invalid, or at least not represent
 *      the state of processed/unprocessed nodes.
 */
trait Registry {
  protected val context: inox.Context
  import context.reporter

  implicit val debugSection = DebugSectionRegistry

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
   *         and insert them all in the graph as usual (see [[checkpoint]]).
   * FIXME However, this adds a BIG assumption on the runtime: no new class should be available!
   *       So, maybe we just don't want that???
   *
   * TODO when caching is implemented further in the pipeline, s/Option/Seq/.
   */
  def update(classes: Seq[xt.ClassDef], functions: Seq[xt.FunDef]): Option[xt.Symbols] = synchronized {
    if (hasPersistentCache) {
      deferredClasses ++= classes
      deferredFunctions ++= functions
      deferredNodes ++= classes map { cd => cd.id -> Left(cd) }
      deferredNodes ++= functions map { fd => fd.id -> Right(fd) }
      None
    } else updateImpl(classes, functions)
  }

  /**
   * To be called once every compilation unit were extracted.
   */
  def checkpoint(): Option[xt.Symbols] = synchronized {
    if (hasPersistentCache) {
      val res = process(deferredClasses, deferredFunctions)
      persistentCache = None // remove the persistent cache after it's used once, the ICG can take over from here.
      deferredClasses.clear()
      deferredFunctions.clear()
      deferredNodes.clear()
      frozen = true
      graph.freeze() // (re-)freeze for next cycle
      res
    } else checkpointImpl()
  }

  /** Import the canonical form cache from the given file. Not thread-safe. */
  def loadCache(file: File): Unit = synchronized {
    val stream = new FileInputStream(file)

    def assertValidCache(check: Boolean) = {
      if (!check) reporter.fatalError(s"Invalid cache file $file")
    }

    def readBytes(size: Int): Array[Byte] = {
      require(size > 0)
      val bytes = new Array[Byte](size)
      assertValidCache(size == stream.read(bytes))
      bytes
    }

    def readInt(): Int = {
      val bytes = readBytes(4)
      BigInt(bytes).intValue
    }

    def readBool(): Boolean = {
      val b = stream.read()
      assertValidCache(b == 0 || b == 1)
      b == 1
    }

    def readId(): Identifier = {
      val len = readInt()
      assertValidCache(len >= 0)
      val idBytes = readBytes(len)
      val globalId = readInt()
      val id = readInt()
      val name = new String(idBytes)
      new Identifier(name, globalId, id)
    }

    try {
      val count = readInt()
      assertValidCache(count >= 0)
      reporter.debug(s"Reading $count pairs from ${file.getAbsolutePath}")
      val mapping = MutableMap[Identifier, (CanonicalForm, Boolean, Int)]()

      for { _ <- 0 until count } {
        val id = readId()
        val checked = readBool()
        val size = readInt()
        assertValidCache(size >= 0)
        val bytes = readBytes(size)
        val depsHash = readInt()

        mapping += id -> (new CanonicalForm(bytes), checked, depsHash)
      }

      persistentCache = Some(mapping.toMap)
    } finally {
      stream.close()
    }
  }

  /** Export the canonical form cache to the given file. Not thread-safe. */
  def saveCache(file: File): Unit = synchronized {
    val stream = new FileOutputStream(file)

    def writeInt(x: Int): Unit = {
      val bi = BigInt(x)
      val repr = bi.toByteArray
      val pad: Byte = if (x < 0) 0xFF.toByte else 0x00
      val bytes = repr.reverse.padTo(4, pad).reverse
      assert(bytes.size == 4)
      stream.write(bytes)
    }

    def writeBool(b: Boolean): Unit = {
      stream.write(if (b) 1 else 0)
    }

    def writeId(id: Identifier): Unit = {
      val idBytes = id.name.getBytes
      val len = idBytes.size
      writeInt(len)
      stream.write(idBytes)
      writeInt(id.globalId)
      writeInt(id.id)
    }

    def getId(node: NodeValue) = node match {
      case Left(cd) => cd.id
      case Right(fd) => fd.id
    }

    def isChecked(node: NodeValue) = node match {
      case Left(cd) => shouldBeChecked(cd)
      case Right(fd) => shouldBeChecked(fd)
    }

    val localCFCache = MutableMap[Identifier, CanonicalForm]() // cache CanonicalForm and their hash.
    def getCF(node: NodeValue): CanonicalForm = localCFCache.getOrElseUpdate(getId(node), buildCF(node))

    var failure = false
    try {
      // For each (id, cf) in cache, save the related data.
      val nodes = graph.getNodes
      reporter.debug(s"Saving ${nodes.size} pairs to ${file.getAbsolutePath}")
      writeInt(nodes.size)
      nodes foreach { case (id, (node, deps)) =>
        val cf = getCF(node)
        val checked = isChecked(node)

        writeId(id)
        writeBool(checked)
        writeInt(cf.bytes.size)
        stream.write(cf.bytes)

        // For dependencies, we store only the hash of the sorted hashes for each dependency
        // TODO Instead of storing the hash, we could have a "generation ID", a bit like a versioning system.
        val hashes = deps.toSeq map { dep => getCF(nodes(dep)._1).hashCode }
        writeInt(hashes.sorted.hashCode)
      }
    } catch {
      case e: IOException =>
        reporter.error(s"The registry cache couldn't be written to ${file.getAbsolutePath}, reason: $e")
        failure = true
    } finally {
      stream.close()
      if (failure) file.delete()
    }
  }


  /******************* Customisation Points *******************************************************/

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

  // Data that is known to be "alive" (i.e. added/updated/maintained in the last cycle).
  private val recentClasses = ListBuffer[xt.ClassDef]()
  private val recentFunctions = ListBuffer[xt.FunDef]()

  private val knownOpenClasses = MutableMap[Identifier, xt.ClassDef]()

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
      val cf1 = cfCache.getOrElseUpdate(id, buildCF(oldInput))
      val cf2 = buildCF(newInput)

      cfCache += id -> cf2

      cf1 == cf2
    }
  }

  private def buildCF(node: NodeValue) = node match {
    case Left(cd) => CanonicalFormBuilder(cd)
    case Right(fd) => CanonicalFormBuilder(fd)
  }

  // See note about persistent cache at the top.
  private var persistentCache: Option[Map[Identifier, (CanonicalForm, Boolean, Int)]] = None
  private def hasPersistentCache = persistentCache.isDefined
  private val deferredClasses = ListBuffer[xt.ClassDef]()
  private val deferredFunctions = ListBuffer[xt.FunDef]()
  private val deferredNodes = MutableMap[Identifier, NodeValue]()

  private def isOfInterest(node: NodeValue, deps: Set[Identifier]): Boolean = {
    val id = node match {
      case Left(cd) => cd.id
      case Right(fd) => fd.id
    }

    def default = node match {
      case Left(cd) => shouldBeChecked(cd)
      case Right(fd) => shouldBeChecked(fd)
    }

    // If we have a cache (first cycle only), check if the node was already computed.
    val result = persistentCache match {
      case None =>
        reporter.debug(s"fallback on default for $id")
        default

      case Some(cache) =>
        val (id, cf) = node match {
          case Left(cd) => cd.id -> CanonicalFormBuilder(cd)
          case Right(fd) => fd.id -> CanonicalFormBuilder(fd)
        }

        cache.get(id) match {
          case None =>
            reporter.debug(s"fallback on default for $id, NOT IN CACHE")
            default

          case Some((cachedCf, checked, hash)) =>
            // Compute the hashes of the extracted nodes with the hashes from the persistent cache.
            // Mind the fact that we need to know all the definitions to compute the hash.
            val hashes = deps.toSeq map deferredNodes map buildCF map { _.hashCode }
            val currentHash = hashes.sorted.hashCode
            reporter.debug(
              s"from cache for $id -> checked? $checked, equals? ${cachedCf == cf}, hash? ${hash == currentHash}"
            )
            (!checked || cachedCf != cf || hash != currentHash) && default
        }
    }

    reporter.debug(s"verdict for $id? $result")

    result
  }

  private def updateImpl(classes: Seq[xt.ClassDef], functions: Seq[xt.FunDef]): Option[xt.Symbols] = {
    def isReady(cd: xt.ClassDef): Boolean = getTopLevels(classes, cd) match {
      case Some(tops) if tops.isEmpty =>
        (cd.flags contains xt.IsSealed) || // Explicitly sealed is good.
        !(cd.flags contains xt.IsAbstract) // Because we do not allow inheriting from case classes.
      case Some(tops) =>
        tops forall { top => top.flags contains xt.IsSealed } // All parents must be sealed.
      case None =>
        false // Some parents are in different compilation unit, hence not ready.
    }

    recentClasses ++= classes
    recentFunctions ++= functions

    val (ready, open) = classes partition isReady
    knownOpenClasses ++= open map { cd => cd.id -> cd }

    classes foreach { cd =>
      if ((cd.flags contains xt.IsAbstract) && !(cd.flags contains xt.IsSealed))
        reporter.warning(cd.getPos, s"Consider sealing ${cd.id}.")
    }

    process(ready, functions)
  }


  private def checkpointImpl(): Option[xt.Symbols] = {
    // Get all nodes from graph, remove the ones not in recentClasses or recentFunctions.
    val nodes = graph.getNodes map { _._2._1 }
    val toRemove = nodes collect {
      case Left(cd) if !(recentClasses contains cd) => cd.id
      case Right(fd) if !(recentFunctions contains fd) => fd.id
    }

    reporter.debug(s"Removing <${toRemove map { _.uniqueName } mkString ", "}> from graph")

    toRemove foreach graph.remove

    recentClasses.clear()
    recentFunctions.clear()

    val defaultRes = process(knownOpenClasses.values.toSeq, Seq.empty)
    val res = if (frozen) {
      assert(defaultRes.isEmpty)
      graph.unfreeze() map { case (cls, funs) => xt.NoSymbols.withClasses(cls.toSeq).withFunctions(funs.toSeq) }
    } else {
      frozen = true
      defaultRes
    }

    graph.freeze() // (re-)freeze for next cycle

    val missings = graph.getMissing
    if (missings.nonEmpty) {
      graph.getNodes foreach { case (id, (node, deps)) =>
        if ((deps & missings).nonEmpty) {
          val unknowns = (deps & missings) map { _.uniqueName } mkString ", "
          reporter.error(s"${id.uniqueName} depends on missing dependencies: $unknowns.")
          reporter.debug(node)
        }
      }
      reporter.internalError(s"Missing some nodes in Registry: ${missings map { _.uniqueName } mkString ", "}")
    }

    res
  }

  private def process(classes: Seq[xt.ClassDef], functions: Seq[xt.FunDef]): Option[xt.Symbols] = {
    // Compute direct dependencies and insert the new information into our dependency graph
    val clusters = computeClusters(classes)
    val invariants = computeInvariantMapping(functions)
    val methods = computeMethodMapping(functions)
    def computeAllDirectDependencies(cd: xt.ClassDef) =
      computeDirectDependencies(cd) ++ clusters(cd) ++ invariants(cd) ++ methods(cd)

    val newNodes: Seq[(Identifier, NodeValue, Set[Identifier])] =
      (classes map { cd => (cd.id, Left(cd): NodeValue, computeAllDirectDependencies(cd)) }) ++
      (functions map { fd => (fd.id, Right(fd): NodeValue, computeDirectDependencies(fd)) })

    // Critical Section
    val results: Seq[Result] = this.synchronized {
      newNodes flatMap { case (id, input, deps) => graph.update(id, input, deps, isOfInterest(input, deps)) }
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
      reporter.internalError(s"Couldn't find parent $parent of $id in <${universe map { _.id } mkString ", "}>")
  }


  private case class IncompleteHierarchy(cd: Identifier, parent: Identifier, classes: Seq[xt.ClassDef]) extends Throwable
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
    //  - project the function onto its id;
    //  - group info by class id;
    //  - ensures that at most one invariant is defined by class.
    val db: Map[Identifier, Option[Identifier]] =
      functions collect {
        case fd if fd.flags contains xt.IsInvariant =>
          val cid = fd.flags collectFirst { case xt.IsMethodOf(id) => id } getOrElse {
            reporter.internalError(s"Expected to find a IsMethodOf flag for invariant function ${fd.id}")
          }

          cid -> fd.id
      } groupBy {
        case (cid, fid) => cid
      } map { case (cid, xs) =>
        val fids = xs map { _._2 } // Map cid -> Seq[fid]
        if (fids.size != 1) {
          reporter.internalError(s"Expected to find one invariant for class $cid, got <${fids mkString ", "} >.")
        }

        cid -> Some(fids.head)
      }

    (cd: xt.ClassDef) => { db.getOrElse(cd.id, None) }
  }

  /**
   * Compute a (total) mapping, solely based on the given [[functions]], to identify
   * class dependency toward their methods, if any.
   */
  private def computeMethodMapping(functions: Seq[xt.FunDef]): xt.ClassDef => Seq[Identifier] = {
    // cid -> fid* mapping
    val db: Map[Identifier, Seq[Identifier]] =
      functions collect {
        case fd if fd.flags exists { case xt.IsMethodOf(_) => true; case _ => false } =>
          val Some(cid) = fd.flags collectFirst { case xt.IsMethodOf(cid) => cid }
          cid -> fd.id
      } groupBy {
        case (cid, fid) => cid
      } map {
        case (cid, xs) => cid -> (xs map { _._2 })
      }

    (cd: xt.ClassDef) => { db.getOrElse(cd.id, Seq.empty) }
  }

}

