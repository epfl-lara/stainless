/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package verification

import extraction.xlang.{ trees => xt }
import utils.{ DependenciesFinder, IncrementalComputationalGraph }

import scala.collection.mutable.{ ListBuffer }

/** Callback for verification */
class VerificationCallBack(val ctx: inox.Context) extends frontend.CallBack {

  /** Keep track of the valid data as they come, in a thread-safe fashion. */
  private object Registry {
    private type NodeValue = Either[xt.ClassDef, xt.FunDef] // "Union" type.

    private type Result = (Set[xt.ClassDef], Set[xt.FunDef])
    private val EmptyResult = (Set[xt.ClassDef](), Set[xt.FunDef]())

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
     */
    def update(classes: Seq[xt.ClassDef], functions: Seq[xt.FunDef]): Seq[xt.Symbols] = {
      // Compute direct dependencies and insert the new information into our dependency graph
      val newNodes: Seq[(Identifier, NodeValue, Set[Identifier])] =
        (classes map { cd => (cd.id, Left(cd): NodeValue, computeDirectDependencies(cd)) }) ++
        (functions map { fd => (fd.id, Right(fd): NodeValue, computeDirectDependencies(fd)) })

      // Critical Section
      val results: Seq[Result] =
        this.synchronized {
          newNodes flatMap { case (id, input, deps) => graph.update(id, input, deps) }
        }

      results flatMap { case (cls, funs) =>
        val isOfInterest = (cls exists shouldBeChecked) || (funs exists shouldBeChecked)
        if (isOfInterest) Some(xt.NoSymbols.withClasses(cls.toSeq).withFunctions(funs.toSeq))
        else None
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
  private def computeDirectDependencies(fd: xt.FunDef): Set[Identifier] = (new DependenciesFinder)(fd)
  private def computeDirectDependencies(cd: xt.ClassDef): Set[Identifier] = (new DependenciesFinder)(cd)

  override def apply(file: String, unit: xt.UnitDef,
                     classes: Seq[xt.ClassDef], functions: Seq[xt.FunDef]): Unit = {
    ctx.reporter.info(s"Got a unit for $file:${unit.id}") // Make this debug

    Registry.update(classes, functions) foreach { syms =>
      // The registry tells us something should be verified in these symbols.
      val program = new inox.Program {
        val trees: extraction.xlang.trees.type = extraction.xlang.trees
        val ctx = VerificationCallBack.this.ctx
        val symbols = syms
      }

      // TODO remove this in favor of a the more general "ensureWellFormed" below.
      for ((_, fd) <- syms.functions) {
        try {
          syms.typeCheck(fd.fullBody, fd.returnType)
        } catch {
          case e: syms.TypeErrorException =>
            ctx.reporter.error(e.pos, e.getMessage)

            ctx.reporter.error(
              s"Function doesn't typecheck:\n" +
              syms.explainTyping(fd.fullBody)(xt.PrinterOptions.fromContext(ctx))
            )

            val deps = computeDirectDependencies(fd)
            ctx.reporter.error(s"Detected dependencies are: " + (deps mkString ", "))

            ctx.reporter.error(s"Available functions: " + (syms.functions.values map { _.id } mkString ", "))
            ctx.reporter.error(s"Available classes: " + (syms.classes.values map { _.id } mkString ", "))

            ctx.reporter.fatalError(s"The extracted sub-program in not well typed.")
        }
      }

      try {
        syms.ensureWellFormed
        ctx.reporter.info(s"The sub-program is well formed.")
      } catch {
        case e: syms.TypeErrorException =>
          ctx.reporter.error(e.pos, e.getMessage)
          ctx.reporter.fatalError(s"The extracted sub-program in not well formed.")
      }

      solve(program)
    }
  }

  private type Report = verification.VerificationComponent.Report
  private val tasks = ListBuffer[java.util.concurrent.Future[Report]]()

  private def solve(program: Program { val trees: extraction.xlang.trees.type }): Unit = {
    // Dispatch a task to the executor service instead of blocking this thread.
    val task = new java.util.concurrent.Callable[Report] {
      override def call(): Report = try {
        verification.VerificationComponent(program)
      } catch {
        case e: Throwable =>
          ctx.reporter.error(s"VerificationComponent failed: $e")
          throw e
      }
    }

    // val future = MainHelpers.executor.submit(task)
    // this.synchronized { tasks += future }
    task.call() // For debug, comment the two previous lines and uncomment this one.
  }

  override def stop(): Unit = tasks foreach { _.cancel(true) }

  override def join(): Unit = tasks foreach { _.get }

  // See assumption/requirements in [[CallBack]]
  // FIXME maybe instead of several report we should merge them?
  override def getReports = tasks map { _.get } filter { _ != null }
}


