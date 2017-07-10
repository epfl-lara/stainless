/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package verification

import extraction.xlang.{ trees => xt }
import utils.{ DependenciesFinder, IncrementalComputationalGraph }

import scala.collection.mutable.{ ListBuffer, Map => MutableMap }

/** Callback for verification */
class VerificationCallBack(val ctx: inox.Context) extends frontend.CallBack {

  /** Keep track of the valid data as they come, in a thread-safe fashion. */
  private object Registry {
    private type NodeValue = Either[xt.ClassDef, xt.FunDef] // "Union" type.

    private type Result = (Set[xt.ClassDef], Set[xt.FunDef])
    private val EmptyResult = (Set[xt.ClassDef](), Set[xt.FunDef]())

    private val knownClasses = MutableMap[Identifier, xt.ClassDef]()

    // TODO Are Identifier okay? We might have some issue with how they are compared due
    //      to the global/id counters...
    private val graph = new IncrementalComputationalGraph[Identifier, NodeValue, Result] {
      override def compute(ready: Set[(Identifier, NodeValue)]): Result = {
        (EmptyResult /: ready) { case ((cls, funs), (id, node)) =>
          node match {
            case Left(cd) => (cls + cd, funs)
            case Right(fd) => (cls, funs + fd)
          }
        }
      }

      /*
       * override def equivalent(id: Identifier, deps: Set[Identifier],
       *                         oldInput: NodeValue, newInput: NodeValue): Boolean = {
       *   // TODO avoid recompute things that are equivalent.
       *   // Karine Perrard's work might be of interest here.
       * }
       */
    }


    /**
     * Update the graph with the new/updated classes and functions.
     *
     * With the new information, if something is ready to be verified, [[update]] returns
     * sequences of self-contained symbols required for verification.
     *
     * TODO currently, the resulting set of symbols is an over-approximation:
     *      there can be some elements that actually don't need to be verified in the set
     *      and are not required to be in the set to verify the elements that should
     *      be verified. To improve on this, [[IncrementalComputationalGraph]] needs to
     *      have "shouldCompute" predicates -- essentially the same as [[shouldBeChecked]].
     *
     * NOTE distinguish sealed and non-sealed class hierarchies. Handle the latter appropriately.
     *      To do that, we can:
     *       - delay the insertion of classes in the graph,
     *       - once notified that everything was compiled, consider all classes as sealed,
     *         and insert them all in the graph as usual.
     * FIXME However, this adds a BIG assumption on the runtime: no new class should be available!
     *       So, maybe we just don't want that???
     */
    def update(classes: Seq[xt.ClassDef], functions: Seq[xt.FunDef]): Option[xt.Symbols] = {
      def isSealed(cd: xt.ClassDef): Boolean = {
        val tops = {
          val parents = getTopLevels(classes, cd)
          if (parents.nonEmpty) parents else Set(cd) // Consider the class itself if it has no parents
        }

        tops forall { top => top.flags contains xt.IsSealed }
      }

      val (ready, open) = classes partition isSealed
      this.synchronized {
        knownClasses ++= open map { cd => cd.id -> cd }
      }

      classes foreach { cd =>
        if ((cd.flags contains xt.IsAbstract) && !(cd.flags contains xt.IsSealed))
          ctx.reporter.warning(cd.getPos, s"Consider sealing ${cd.id}")
      }

      process(ready, functions)
    }

    /**
     * To be called once every compilation unit where extracted.
     */
    def checkpoints(): Option[xt.Symbols] = process(knownClasses.values.toSeq, Seq.empty)

    private def process(classes: Seq[xt.ClassDef], functions: Seq[xt.FunDef]): Option[xt.Symbols] = {
      // Compute direct dependencies and insert the new information into our dependency graph
      val clusters = computeClusters(classes)
      val newNodes: Seq[(Identifier, NodeValue, Set[Identifier])] =
        (classes map { cd => (cd.id, Left(cd): NodeValue, computeDirectDependencies(cd) ++ clusters(cd)) }) ++
        (functions map { fd => (fd.id, Right(fd): NodeValue, computeDirectDependencies(fd)) })

      // Critical Section
      val results: Seq[Result] =
        this.synchronized {
          newNodes flatMap { case (id, input, deps) => graph.update(id, input, deps) }
        }

      // TODO this filter should be moved into the graph
      val ofInterest =
        results filter { case (cls, funs) => (cls exists shouldBeChecked) || (funs exists shouldBeChecked) }

      if (ofInterest.isEmpty) None
      else {
        // Group into one set of Symbols to avoid verifying the same things several times
        // TODO this is just because we don't have caching later on in the pipeline (YET).
        val (clsSets, funsSets) = ofInterest.unzip
        val cls = (Set[xt.ClassDef]() /: clsSets) { _ union _ }
        val funs = (Set[xt.FunDef]() /: funsSets) { _ union _ }
        Some(xt.NoSymbols.withClasses(cls.toSeq).withFunctions(funs.toSeq))
      }
    }

    /**
     * We create "clusters" for classes:
     * they define class hierarchies based on the given subset of all classes.
     */
    private type ClusterMap = Map[xt.ClassDef, Set[Identifier]]
    private def computeClusters(classes: Seq[xt.ClassDef]): ClusterMap = {
      // Record mapping "cd.topParent -> _ += cd" for each top level parent class.
      def record(acc: ClusterMap, cd: xt.ClassDef): ClusterMap = {
        (acc /: getTopLevels(classes, cd)) { (acc, top) =>
          val currentCluster = acc.getOrElse(top, Set[Identifier]())
          val newCluster = currentCluster + cd.id
          acc + (top -> newCluster)
        }
      }

      // From the top level, propagate information to the leaves.
      val EmptyClusters = Map[xt.ClassDef, Set[Identifier]]()
      val topLevelClusters = (EmptyClusters /: classes) { record(_, _) }
      classes map { cd =>
        val parents = getTopLevels(classes, cd) map topLevelClusters
        val cluster = (Set[Identifier]() /: parents) { _ union _ }
        cd -> (cluster - cd.id)
      }
    }.toMap

    // Find the top level parents for the given class, returns empty seq when no inheritance.
    private def getTopLevels(classes: Seq[xt.ClassDef], cd0: xt.ClassDef): Set[xt.ClassDef] = {
      def getDirects(cd: xt.ClassDef): Set[xt.ClassDef] = cd.parents.toSet map { ct: xt.ClassType =>
        classes find { _.id == ct.id } getOrElse {
          val error = s"Expected to find parent in the given classes! (${ct.id.uniqueName} for ${cd.id.uniqueName}, in " +
                      s"${classes map { _.id.uniqueName } mkString ", "})"
          ctx.reporter.fatalError(error)
        }
      }

      if (cd0.parents.isEmpty) Set.empty else {
        getDirects(cd0) flatMap { p => if (p.parents.isEmpty) Set(p) else getTopLevels(classes, p) }
      }
    }


  }

  /** Checks whether the given function/class should be verified at some point. */
  // TODO this check should be moved to a utility package and copy/past code removed from stainless.
  private def shouldBeChecked(fd: xt.FunDef): Boolean = {
    val isLibrary = fd.flags contains "library"
    val isUnchecked = fd.flags contains "unchecked"
    !(isLibrary || isUnchecked)
    // TODO check --functions=... options for proper filter
  }

  private def shouldBeChecked(cd: xt.ClassDef): Boolean = {
    true // TODO
  }

  /** Compute the set of direct, non-recursive dependencies of the given [[xt.FunDef]] or [[xt.ClassDef]]. */
  private def computeDirectDependencies(fd: xt.FunDef): Set[Identifier] = new DependenciesFinder()(fd)
  private def computeDirectDependencies(cd: xt.ClassDef): Set[Identifier] = new DependenciesFinder()(cd)

  override def beginExtractions(): Unit = { /* nothing */ }

  override def apply(file: String, unit: xt.UnitDef,
                     classes: Seq[xt.ClassDef], functions: Seq[xt.FunDef]): Unit = {
    ctx.reporter.info(s"Got a unit for $file:${unit.id}") // Make this debug

    val symss = Registry.update(classes, functions)
    processSymbols(symss)
  }

  override def endExtractions(): Unit = {
    val symss = Registry.checkpoints()
    processSymbols(symss)
  }

  private def processSymbols(symss: Iterable[xt.Symbols]): Unit = symss foreach { syms =>
    // The registry tells us something should be verified in these symbols.
    val program = new inox.Program {
      val trees: extraction.xlang.trees.type = extraction.xlang.trees
      val ctx = VerificationCallBack.this.ctx
      val symbols = syms
    }

    try {
      syms.ensureWellFormed
    } catch {
      case e: syms.TypeErrorException =>
        ctx.reporter.error(e.pos, e.getMessage)
        ctx.reporter.fatalError(s"The extracted sub-program in not well formed.")
    }

    solve(program)
  }

  private type Report = verification.VerificationComponent.Report
  private val tasks = ListBuffer[java.util.concurrent.Future[Report]]()

  private def solve(program: Program { val trees: extraction.xlang.trees.type }): Unit = {
    // Dispatch a task to the executor service instead of blocking this thread.
    val task = new java.util.concurrent.Callable[Report] {
      override def call(): Report = verification.VerificationComponent(program)
    }

    val future = MainHelpers.executor.submit(task)
    this.synchronized { tasks += future }
    // task.call() // For debug, comment the two previous lines and uncomment this one.
  }

  override def stop(): Unit = tasks foreach { _.cancel(true) }

  override def join(): Unit = tasks foreach { _.get }

  // See assumption/requirements in [[CallBack]]
  override def getReports = tasks map { _.get } filter { _ != null }

}


