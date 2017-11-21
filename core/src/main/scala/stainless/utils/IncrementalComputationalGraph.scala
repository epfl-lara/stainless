/* Copyright 2009-2016 EPFL, Lausanne */

package stainless.utils

import scala.collection.mutable.{ Map => MutableMap, Set => MutableSet, Queue => MutableQueue }

/**
 * Describe a Graph of Computation that is incrementally refined/updated. [[Node]]s can be inserted
 * (and updated) sequentially to build a full graph. After each [[update]], [[compute]] is called at
 * most once with the set of all nodes not yet computed -- which (indirect, possibly cyclic) dependencies
 * are all known -- with the dependencies themselves, hence a node might be passed to [[compute]]
 * several times.
 *
 * When any dependency of a node is updated, the node is recomputed unless its [[compute]] flag is
 * turned off.
 *
 * Before entering an invalid state for the graph, one can [[freeze]] it and then [[unfreeze]] the
 * graph to resume computation.
 */
trait IncrementalComputationalGraph[Id, Input, Result] {

  /******************* Public Interface ***********************************************************/

  /**
   * Insert (or override) a given node into the graph, then perform computation
   * based on the graph state. Return the computed values.
   *
   * When [[compute]] is false the node doesn't trigger a call to [[compute]] when
   * all the [[deps]] -- and the indirect dependencies -- are present in the graph.
   */
  def update(id: Id, in: Input, deps: Set[Id], compute: Boolean): Option[Result] = {
    update(Node(id, in, deps, compute))
  }

  /**
   * Remove a node from the graph.
   *
   * Throw an [[java.lang.IllegalArgumentException]] if the node wasn't in the graph.
   */
  def remove(id: Id): Unit = nodes get id match {
    case Some(n) => remove(n)
    case None => throw new java.lang.IllegalArgumentException(s"Node $id is not part of the graph")
  }

  /** Put on hold any computation. */
  def freeze(): Unit = {
    frozen = true
  }

  /** Resume computation. */
  def unfreeze(): Option[Result] = {
    frozen = false
    process()
  }

  /** Get a read-only version of the graph. */
  def getNodes: Map[Id, (Input, Set[Id])] = nodes.toMap map { case (id, n) => (id, n.in -> n.deps) }

  /** Get the current missing nodes' identifier from the graph. */
  def getMissing: Set[Id] = allIds.toSet -- nodes.keySet


  /******************* Customisation Points *******************************************************/

  /**
   * Produce some result for the set of nodes that are all ready.
   *
   * It is guaranteed that [[ready]] contains all the dependencies for all element of [[ready]].
   *
   * The result itself is not used by [[IncrementalComputationalGraph]].
   */
  protected def compute(ready: Set[(Id, Input)]): Result

  /**
   * Determine whether the new value for a node is equivalent to the old value, given that
   * they have the same id (enforced by the graph model) and the same set of dependencies.
   */
  protected def equivalent(id: Id, deps: Set[Id], oldInput: Input, newInput: Input): Boolean


  /******************* Implementation *************************************************************/

  /**
   * Representation of a [[Node]]:
   *  - Its [[id]] fully identifies a node (i.e. two nodes are equal <=> their ids are equal).
   *    This allows overriding a node simply by inserting a new node with the same identifier.
   *  - [[in]] denotes the input value for the node which is used for the computation.
   *  - [[deps]] holds the set of **direct** dependencies.
   *  - [[compute]] determines whether the node should trigger a computation on its own or not.
   * Indirect dependencies is computed by [[IncrementalComputationalGraph]] itself.
   */
  private case class Node(id: Id, in: Input, deps: Set[Id], compute: Boolean) {
    override def equals(any: Any): Boolean = any match {
      case Node(other, _, _, _) => id == other
      case _ => false
    }

    override def hashCode: Int = id.hashCode
  }

  /**
   * Implementation for the public [[update]] function.
   *
   * If the new node is equivalent to an old one, do nothing. Otherwise, process normally.
   * Note that, when any of its dependencies is updated the (new) node is put in the
   * [[toCompute]] set.
   */
  private def update(n: Node): Option[Result] = nodes get n.id match {
    case Some(m) if (m.deps == n.deps) && equivalent(n.id, n.deps, m.in, n.in) =>
      // Nothing new, but update the node anyway -- equivalence != equality.
      nodes += n.id -> n
      None

    case mOpt =>
      val replace = mOpt.isDefined
      if (replace) remove(n)
      insert(n)
      if (frozen) None else process()
  }

  /** Flag used to pause the computation. */
  private var frozen = false

  /**
   * Some nodes might not yet be fully known, yet we have some evidence (through other nodes'
   * dependencies) that they exists. We therefore keep track of dependencies using their
   * identifiers, and we keep track of the mapping between identifiers and nodes in [[nodes]].
   */
  private val nodes = MutableMap[Id, Node]()
  private val allIds = MutableSet[Id]()

  /* The set of nodes not yet computed, but seen. */
  private val toCompute = MutableSet[Node]()

  /*
   * A reverse graph of dependencies. Because we might not fully know the node yet.
   * we use the known identifiers for the mapping.
   */
  private val reverse = MutableMap[Id, MutableSet[Node]]()


  def toDot(filename: String, idPrinter: Id => String, color: Input => String): Unit = {
    import java.io._
    val dot = toDotGraph(idPrinter, color)
    val pw = new PrintWriter(new File(filename))
    try pw.write(dot) finally pw.close()
  }

  private def toDotGraph(idPrinter: Id => String, color: Input => String): String = {
    assert(getMissing.isEmpty) // Case not handled.

    val sb = new StringBuilder

    // Header
    sb ++= "digraph ICG {\nnode [style=filled];\n"

    // Nodes for colors
    for {
      n <- nodes.values
    } sb ++= s""""${idPrinter(n.id)}" [color=${color(n.in)}];\n"""

    // Nodes & edges
    for {
      (to, froms) <- reverse
      from <- froms
    } sb ++= s""""${idPrinter(from.id)}" -> "${idPrinter(to)}"\n"""

    // Footer
    sb ++= "}"

    sb.toString
  }

  /**
   * Insert a new node & update the graph,
   * placing any node that depends on [[n]] into [[toCompute]]
   */
  private def insert(n: Node): Unit = {
    allIds += n.id
    allIds ++= n.deps
    nodes += n.id -> n
    if (n.compute) toCompute += n
    n.deps foreach { depId =>
      reverse.getOrElseUpdate(depId, MutableSet()) += n
    }

    mark(n)
  }

  /** Remove an existing node from the graph. */
  private def remove(n: Node): Unit = {
    allIds -= n.id
    nodes -= n.id
    toCompute -= n
    reverse.values foreach { _ -= n }
  }

  /** Recursively put the nodes that depends on [[n]] into [[toCompute]]. */
  private def mark(n: Node): Unit = {
    val seen = MutableSet[Node]()
    val queue = MutableQueue[Node]()

    // Add nodes that depend on n to the queue, if not yet visited
    def add(n: Node): Unit = {
      reverse get n.id foreach { sǝᴉɔuǝpuǝdǝp =>
        queue ++= sǝᴉɔuǝpuǝdǝp filterNot seen
      }
    }

    // Visit a node and queue the ones that depend on it.
    def visit(n: Node): Unit = if (seen contains n) { /* visited via another path */ } else {
      seen += n
      if (n.compute) toCompute += n

      add(n)
    }

    // Start visiting the node itself, then loop until all nodes that
    // depend on it are visited.
    visit(n)
    while (queue.nonEmpty) {
      val head = queue.dequeue
      visit(head)
    }
  }

  /** Determine the set of nodes that can be computed, and compute them. */
  private def process(): Option[Result] = {
    val ready: Set[Node] = {
      val setOfSet = for {
        n <- toCompute
        allDeps <- dependencies(n)
      } yield allDeps

      if (setOfSet.isEmpty) Set()
      else setOfSet reduce { _ union _ }
    }

    toCompute --= ready
    if (ready.isEmpty) None
    else {
      val args = ready map { n => (n.id, n.in) }
      Some(compute(args))
    }
  }

  /**
   * Compute the set of (indirect or not) dependencies,
   * or return None if any dependency is missing from the graph.
   */
  private def dependencies(n: Node): Option[Set[Node]] = {
    val seen = MutableSet[Node]()
    val deps = MutableSet[Node]()
    val queue = MutableQueue[Node]()
    var complete = true

    // Called when we have a missing dependency.
    def abort(): Unit = {
      complete = false
    }

    // Visit this node, and queue its dependencies when we have all of them, abort otherwise.
    def visit(n: Node): Unit = if (seen contains n) { /* visited via another path */ } else {
      seen += n
      deps += n

      if (n.deps subsetOf nodes.keySet) {
        val nexts = n.deps map nodes filterNot seen
        queue ++= nexts
      } else abort()
    }

    visit(n)
    while (complete && queue.nonEmpty) {
      val head = queue.dequeue
      visit(head)
    }

    if (complete) Some(deps.toSet)
    else None
  }

}

