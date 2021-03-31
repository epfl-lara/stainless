/* Copyright 2009-2021 EPFL, Lausanne */

import scala.collection.parallel.ForkJoinTasks
import scala.concurrent.ExecutionContext
import java.util.concurrent.Executors
import java.io.PrintWriter
import java.io.StringWriter

import inox.transformers._
import inox.utils.{Position, NoPosition}

package object stainless {

  object optJson extends inox.OptionDef[String] {
    val name = "json"
    val default = "report.json"
    val parser = inox.OptionParsers.stringParser
    val usageRhs = "file"
  }

  object optWatch extends inox.FlagOptionDef("watch", false)
  def isWatchModeOn(implicit ctx: inox.Context) = ctx.options.findOptionOrDefault(optWatch)

  object optCompact extends inox.FlagOptionDef("compact", false)
  def isCompactModeOn(implicit ctx: inox.Context) = ctx.options.findOptionOrDefault(optCompact)

  type Program = inox.Program { val trees: ast.Trees }

  type StainlessProgram = Program { val trees: stainless.trees.type }

  /** Including these aliases here makes default imports more natural. */
  type Identifier = inox.Identifier
  val FreshIdentifier = inox.FreshIdentifier

  implicit final class IdentifierFromSymbol(id: Identifier) {
    def fullName: String = id match {
      case ast.SymbolIdentifier(name) => name
      case _ => id.name
    }
  }

  implicit final class PositioningWrapper[T <: inox.ast.Trees#Tree](tree: T) {
    def ensurePos(pos: Position): T = if (tree.getPos != NoPosition) tree else tree.setPos(pos)
  }

  object trees extends ast.Trees with inox.ast.SimpleSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      sorts: Map[Identifier, ADTSort]
    ) extends SimpleSymbols with AbstractSymbols

    object printer extends ast.Printer { val trees: stainless.trees.type = stainless.trees }
  }

  implicit val stainlessSemantics: inox.SemanticsProvider { val trees: stainless.trees.type } =
    new inox.SemanticsProvider {
      val trees: stainless.trees.type = stainless.trees

      def getSemantics(p: inox.Program { val trees: stainless.trees.type }): p.Semantics = new inox.Semantics { self =>
        val trees: p.trees.type = p.trees
        val symbols: p.symbols.type = p.symbols
        val program: Program { val trees: p.trees.type; val symbols: p.symbols.type } =
          p.asInstanceOf[Program { val trees: p.trees.type; val symbols: p.symbols.type }]

        protected def createSolver(ctx: inox.Context): inox.solvers.SolverFactory {
          val program: self.program.type
          type S <: inox.solvers.combinators.TimeoutSolver { val program: self.program.type }
        } = solvers.SolverFactory(self.program, ctx)

        protected def createEvaluator(ctx: inox.Context): inox.evaluators.DeterministicEvaluator {
          val program: self.program.type
        } = evaluators.Evaluator(self.program, ctx)
      }.asInstanceOf[p.Semantics] // @nv: unfortunately required here...
    }

  def encodingSemantics(ts: ast.Trees)
                       (transformer: TreeTransformer { val s: ts.type; val t: stainless.trees.type }):
                        inox.SemanticsProvider { val trees: ts.type } = {
    new inox.SemanticsProvider {
      val trees: ts.type = ts

      def getSemantics(p: inox.Program { val trees: ts.type }): p.Semantics = new inox.Semantics { self =>
        val trees: p.trees.type = p.trees
        val symbols: p.symbols.type = p.symbols
        val program: inox.Program { val trees: p.trees.type; val symbols: p.symbols.type } =
          p.asInstanceOf[inox.Program { val trees: p.trees.type; val symbols: p.symbols.type }]

        private object encoder extends {
          val sourceProgram: self.program.type = self.program
          val t: stainless.trees.type = stainless.trees
        } with ProgramEncoder {
          val encoder = transformer
          object decoder extends transformers.TreeTransformer {
            val s: stainless.trees.type = stainless.trees
            val t: trees.type = trees
          }
        }

        protected def createSolver(ctx: inox.Context): inox.solvers.SolverFactory {
          val program: self.program.type
          type S <: inox.solvers.combinators.TimeoutSolver { val program: self.program.type }
        } = solvers.SolverFactory.getFromSettings(self.program, ctx)(encoder)(self.asInstanceOf[self.program.Semantics])

        protected def createEvaluator(ctx: inox.Context): inox.evaluators.DeterministicEvaluator {
          val program: self.program.type
        } = inox.evaluators.EncodingEvaluator(self.program)(encoder)(evaluators.Evaluator(encoder.targetProgram, ctx))
      }.asInstanceOf[p.Semantics] // @nv: unfortunately required here...
    }
  }

  def topLevelErrorHandler(e: Throwable)(implicit ctx: inox.Context): Nothing = {
    e match {
      case extraction.MalformedStainlessCode(tree, msg) => ctx.reporter.error(tree.getPos, msg)
      case _ => ()
    }

    ctx.reporter.error(s"Stainless terminated with an error.")

    val sw = new StringWriter
    e.printStackTrace(new PrintWriter(sw))
    new PrintWriter("stainless-stack-trace.txt") { write(sw.toString); close }

    ctx.reporter.error(
      "Debug output is available in the file `stainless-stack-trace.txt`. " +
      "If the crash is caused by Stainless, you may report your issue on https://github.com/epfl-lara/stainless/issues")

    if (ctx.reporter.debugSections.contains(frontend.DebugSectionStack))
      ctx.reporter.debug(sw.toString)(frontend.DebugSectionStack)
    else
      ctx.reporter.error("You may use --debug=stack to have the stack trace displayed in the output.")

    System.exit(2)
    ??? // unreachable
  }


  /* Parallelism utilities */

  private lazy val nParallel: Option[Int] =
    Option(System.getProperty("parallel"))
      .flatMap(p => scala.util.Try(p.toInt).toOption)

  lazy val useParallelism: Boolean =
    (nParallel.isEmpty || nParallel.exists(_ > 1)) &&
    !System.getProperty("os.name").toLowerCase().contains("mac")

  private lazy val currentThreadExecutionContext: ExecutionContext =
    ExecutionContext.fromExecutor(new java.util.concurrent.Executor {
      def execute(runnable: Runnable) { runnable.run() }
    })

  private lazy val multiThreadedExecutor: java.util.concurrent.ExecutorService =
    nParallel.map(Executors.newFixedThreadPool(_)).getOrElse(ForkJoinTasks.defaultForkJoinPool)
  lazy val multiThreadedExecutionContext: ExecutionContext =
    ExecutionContext.fromExecutor(multiThreadedExecutor)

  implicit def executionContext(implicit ctx: inox.Context): ExecutionContext =
    if (useParallelism && ctx.reporter.debugSections.isEmpty) multiThreadedExecutionContext
    else currentThreadExecutionContext

  def shutdown(): Unit = if (useParallelism) multiThreadedExecutor.shutdown()
}
