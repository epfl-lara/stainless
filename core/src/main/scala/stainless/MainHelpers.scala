/* Copyright 2009-2016 EPFL, Lausanne */

package stainless

import extraction.xlang.{trees => xt}
import utils.IncrementalComputationalGraph

import java.io.{File, PrintWriter}
import scala.collection.mutable.{ ListBuffer, Set => MutableSet }

import org.json4s.JsonAST.JObject
import org.json4s.JsonDSL._
import org.json4s.native.JsonMethods._

object MainHelpers {

  /** Set of all available components.
    *
    * NOTE Keep in sync with [[MainHelpers.callbackFactory]].
    */
  val components: Seq[Component] = Seq(
    verification.VerificationComponent,
    termination.TerminationComponent
  )

  /** Process the extracted units.
    *
    * Compilers are required to call the [[CompilerCallBack.apply]] method after extracting
    * each compilation unit (i.e. a scala file). When a compilation unit is recompiled, the
    * callback deals with any potential invalidation of existing data without blocking the
    * callee's thread.
    *
    * A [[Compiler]] has to [[stop]] its callback at some point.
    *
    * Calling [[getReports]] is valid if and only if:
    *  - the callback has been stopped, and
    *  - the program was not running in "watch" mode.
    */
  trait CompilerCallBack {
    def apply(file: String, unit: xt.UnitDef, classes: Seq[xt.ClassDef], functions: Seq[xt.FunDef]): Unit

    def stop(): Unit = () // by default nothing is done

    def getReports: Seq[AbstractReport]
  }

  /** Abstract compiler, provides all the tools to extract [[xt.UnitDef]]s
    * and send them to [[CompilerCallBack]] whenever they are ready.
    */
  abstract class Compiler(val callback: CompilerCallBack) {
    /** Proceed to extract the trees in a non-blocking way. */
    def run(): Unit

    def isRunning: Boolean

    protected def onStop(): Unit

    /** Stop the compiler (and wait until it has stopped) */
    final def stop(): Unit = {
      callback.stop()
      onStop()
    }

    final def getReports: Seq[AbstractReport] = {
      assert(!isRunning)
      callback.getReports
    }
  }

  /** A Compiler factor which takes as input: context + compiler arguments + callback */
  type CompilerFactory = (inox.Context, Seq[String], CompilerCallBack) => Compiler

}

trait MainHelpers extends inox.MainHelpers {

  import MainHelpers._

  case object Pipelines extends Category
  case object Verification extends Category
  case object Termination extends Category

  object optJson extends inox.OptionDef[String] {
    val name = "json"
    val default = "report.json"
    val parser = inox.OptionParsers.stringParser
    val usageRhs = "file"
  }

  override protected def getOptions = super.getOptions ++ Map(
    optFunctions -> Description(General, "Only consider functions s1,s2,..."),
    evaluators.optCodeGen -> Description(Evaluators, "Use code generating evaluator"),
    codegen.optInstrumentFields -> Description(Evaluators, "Instrument ADT field access during code generation"),
    codegen.optSmallArrays -> Description(Evaluators, "Assume all arrays fit into memory during code generation"),
    verification.optParallelVCs -> Description(Verification, "Check verification conditions in parallel"),
    verification.optFailEarly -> Description(Verification, "Halt verification as soon as a check fails"),
    verification.VerificationComponent.optStrictArithmetic -> Description(Verification, "Check arithmetic operations for unintended behaviour and overflows"),
    inox.optTimeout -> Description(General, "Set a timeout n (in sec) such that\n" +
      "  - verification: each proof attempt takes at most n seconds\n" +
      "  - termination: each solver call takes at most n / 100 seconds"),
    extraction.inlining.optInlinePosts -> Description(General, "Inline postconditions at call-sites"),
    termination.optIgnorePosts -> Description(Termination, "Ignore existing postconditions during strengthening"),
    optJson -> Description(General, "Output verification and termination reports to a JSON file")
  ) ++ MainHelpers.components.map { component =>
    val option = new inox.FlagOptionDef(component.name, false)
    option -> Description(Pipelines, component.description)
  }

  override protected def getCategories = Pipelines +: super.getCategories.filterNot(_ == Pipelines)

  override protected def getDebugSections = super.getDebugSections ++ Set(
    verification.DebugSectionVerification,
    termination.DebugSectionTermination,
    DebugSectionExtraction
  )

  override protected def displayVersion(reporter: inox.Reporter) = {
    reporter.title("Stainless verification tool (https://github.com/epfl-lara/stainless)")
  }

  override protected def getName: String = "stainless"

  /* NOTE: Should be implemented by a generated Main class in each compiler-specific project: */
  protected val extraCompilerArguments: List[String] = Nil
  protected val libraryFiles: List[String]
  protected def factory: CompilerFactory

  // TODO add (optional) customisation points for CallBacks to access intermediate reports

  def main(args: Array[String]): Unit = try {
    val ctx = setup(args)
    val compilerArgs = extraCompilerArguments ++ libraryFiles ++ args.toList.filterNot(_.startsWith("--"))

    val compiler = run(ctx, compilerArgs)

    // When in "watch" mode, no final report is printed as there is no proper end.
    // In fact, we might not even have a full list of VCs to be checked...
    val watch: Boolean = false // TODO add a command line flag for this

    if (watch) {
      // TODO Handle signals to stop the compiler properly
      ???
    } else {
      // Passively wait until the compiler has finished and process reports
      while (compiler.isRunning) { Thread.sleep(100) }

      // Process reports: print summary/export to JSON
      val reports: Seq[AbstractReport] = compiler.getReports
      reports foreach { _.emit() }

      ctx.options.findOption(optJson) foreach { file =>
        val output = if (file.isEmpty) optJson.default else file
        ctx.reporter.info(s"Outputing JSON summary to $output")
        exportJson(reports, output)
      }
    }

    ctx.reporter.whenDebug(inox.utils.DebugSectionTimers) { debug =>
      ctx.timers.outputTable(debug)
    }
  } catch {
    case _: inox.FatalError => System.exit(1)
  }


  /** Given a context (with a reporter) and a compiler factory (which takes care of the input files),
    * proceed to compile, extract, transform and verify the input programs.
    *
    * Select the active components and build callbacks for each of them. Feed that to the compiler factory
    * before running the new compiler.
    *
    * The returned compiler is allowed to run forever in the background, e.g. when wathing for file changes.
    * This function is therefore non-blocking. The callee is required to stop the returned compiler to
    * free resources.
    */
  final def run(ctx: inox.Context, compilerArgs: Seq[String]): Compiler = {
    val activeComponents = getActiveComponents(ctx)
    val activeCallbacks = activeComponents map { c => callbackFactory(c.name, ctx) }

    // Distribute event to active components:
    val masterCallback: CompilerCallBack = new CompilerCallBack {
      override def apply(file: String, unit: xt.UnitDef, classes: Seq[xt.ClassDef], functions: Seq[xt.FunDef]): Unit = {
        for { c <- activeCallbacks } c(file, unit, classes, functions)
      }

      override def stop(): Unit = {
        for { c <- activeCallbacks } c.stop()
      }

      override def getReports: Seq[AbstractReport] = {
        activeCallbacks flatMap { _.getReports }
      }
    }

    // Initiate & run the compiler for our needs.
    val compiler = factory(ctx, compilerArgs, masterCallback)
    compiler.run()

    compiler
  }


  /** Callback for verification */
  private class VerificationCallBack(val ctx: inox.Context) extends CompilerCallBack {
    private val reports = ListBuffer[verification.VerificationComponent.Report]()

    /** Keep track of the valid data as they come, in a thread-safe fashion. */
    private object Registry {
      private type NodeValue = Either[xt.ClassDef, xt.FunDef]

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
       * With the new information, if something is ready to be verified, [[update]] return
       * the set of functions/classes required for the verification.
       *
       * The resulting symbols still need to be extracted to fit [[stainless.extraction.trees]]
       * before being sent to the solver.
       *
       * TODO currently, the resulting set of symbols is an over-approximation:
       *      there can be some elements that actually don't need to be verified in the set
       *      and are not required to be in the set to verify the elements that should
       *      be verified. To improve on this, [[IncrementalComputationalGraph]] needs to
       *      have "shouldCompute" predicates -- essentially the same as [[shouldBeChecked]].
       */
      def update(classes: Seq[xt.ClassDef], functions: Seq[xt.FunDef]): Option[xt.Symbols] = {
        // Compute direct dependencies and insert the new information into our dependency graph
        val newNodes: Seq[(Identifier, NodeValue, Set[Identifier])] =
          (classes map { cd => (cd.id, Left(cd): NodeValue, computeDirectDependencies(cd)) }) ++
          (functions map { fd => (fd.id, Right(fd): NodeValue, computeDirectDependencies(fd)) })

        // Critical Section
        val results: Seq[Result] =
          this.synchronized {
            newNodes flatMap { case (id, input, deps) =>
              /*
               * println(s"updating " + (if (input.isLeft) "class" else "function") +
               *         s" ${id.uniqueName} with dependencies: " + (deps map { _.uniqueName } mkString ", "))
               */
              graph.update(id, input, deps)
            }
          }

        val aggregated: Result = (EmptyResult /: results) { case ((cls1, funs1), (cls2, funs2)) =>
          (cls1 ++ cls2, funs1 ++ funs2)
        }

        val (cls, funs) = aggregated
        val isOfInterest = (cls exists shouldBeChecked) || (funs exists shouldBeChecked)

        ctx.reporter.info(
          s"$isOfInterest - Found ${results.size} results, aggregate to ${cls.size} " +
          s"classes and ${funs.size} functions. The list is: " +
          ((cls map { _.id }) ++ (funs map { _.id }) mkString ", ")
        )

        if (isOfInterest) Some(xt.NoSymbols.withClasses(cls.toSeq).withFunctions(funs.toSeq))
        else None
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
    private def computeDirectDependencies(fd: xt.FunDef): Set[Identifier] = (new DepFinder)(fd)
    private def computeDirectDependencies(cd: xt.ClassDef): Set[Identifier] = (new DepFinder)(cd)

    /** [[DepFinder]] find the set of dependencies for a function/class,
      * it is not thread safe and is designed for one and only one run!
      *
      * It returns only the *direct* dependencies, without the argument itself
      * although it could be a recursive function.
      */
    private class DepFinder {
      private val deps: MutableSet[Identifier] = MutableSet.empty
      private val finder = new xt.TreeTraverser {
        override def traverse(e: xt.Expr): Unit = e match {
          case xt.FunctionInvocation(id, _, _) =>
            deps += id
            super.traverse(e)
          case _ => super.traverse(e)
        }

        override def traverse(pat: xt.Pattern): Unit = pat match {
          case xt.UnapplyPattern(_, id, _, _) =>
            deps += id
            super.traverse(pat)
          case _ => super.traverse(pat)
        }

        override def traverse(tpe: xt.Type): Unit = tpe match {
          case xt.ClassType(id, _) =>
            deps += id
            super.traverse(tpe)
          case _ => super.traverse(tpe)
        }
      }

      def apply(fd: xt.FunDef): Set[Identifier] = {
        finder.traverse(fd)
        deps -= fd.id

        deps.toSet
      }

      def apply(cd: xt.ClassDef): Set[Identifier] = {
        cd.tparams foreach finder.traverse
        cd.parents foreach finder.traverse
        cd.fields foreach finder.traverse
        cd.flags foreach finder.traverse
        deps -= cd.id

        deps.toSet
      }
    }

    override def apply(file: String, unit: xt.UnitDef,
                       classes: Seq[xt.ClassDef], functions: Seq[xt.FunDef]): Unit = {
      ctx.reporter.info(s"Got a unit for $file:${unit.id}")
      Registry.update(classes, functions) foreach { syms =>
        // The registry tells us something should be verified in these symbols.
        val program = new inox.Program {
          val trees: extraction.xlang.trees.type = extraction.xlang.trees
          val ctx = VerificationCallBack.this.ctx
          val symbols = syms
        }

        solve(program)
      }
    }

    private def solve(program: Program { val trees: extraction.xlang.trees.type }): Unit = {
      // TODO dispatch solving
      val report = verification.VerificationComponent(program)
      this.synchronized { reports += report }
    }

    // FIXME maybe instead of several report we should merge them?
    override def getReports: Seq[AbstractReport] = reports
  }


  /** Callback for termination */
  private class TerminationCallBack(val ctx: inox.Context) extends CompilerCallBack {
    override def apply(file: String, unit: xt.UnitDef, classes: Seq[xt.ClassDef], functions: Seq[xt.FunDef]): Unit = ???

    override def getReports: Seq[AbstractReport] = Nil
  }


  /** NOTE Should be in synch with [[MainHelpers.components]]. */
  private def callbackFactory(name: String, ctx: inox.Context): CompilerCallBack = {
    val db = Map[String, inox.Context => CompilerCallBack](
      verification.VerificationComponent.name -> { ctx => new VerificationCallBack(ctx) },
      termination.TerminationComponent.name -> { ctx => new TerminationCallBack(ctx) }
    )

    db(name)(ctx)
  }


  /** Based on the context option, return the list of active component (e.g. verification, termination).
    * By default, return [[stainless.verification.VerificationComponent]].
    */
  private def getActiveComponents(ctx: inox.Context) = {
    val fromOptions = components.filter { c =>
      ctx.options.options.collectFirst {
        case inox.OptionValue(o, value: Boolean) if o.name == c.name => value
      }.getOrElse(false)
    }

    if (fromOptions.isEmpty) {
      Seq(verification.VerificationComponent)
    } else {
      fromOptions
    }
  }


  /** Exports the reports to the given file in JSON format. */
  private def exportJson(reports: Seq[AbstractReport], file: String): Unit = {
    val subs = reports map { r => JObject(r.name -> r.emitJson()) }
    val json = subs reduce { _ ~ _ }
    val string = pretty(render(json))
    val pw = new PrintWriter(new File(file))
    try pw.write(string) finally pw.close()
  }

}

