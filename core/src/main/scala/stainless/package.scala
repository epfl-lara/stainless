/* Copyright 2009-2021 EPFL, Lausanne */

import scala.collection.parallel.ForkJoinTasks
import scala.concurrent.ExecutionContext
import java.util.concurrent.Executors
import java.io.PrintWriter
import java.io.StringWriter
import inox.transformers._
import inox.utils.{NoPosition, Position}

package object stainless {

  object optJson extends inox.OptionDef[String] {
    val name = "json"
    val default = "report.json"
    val parser = inox.OptionParsers.stringParser
    val usageRhs = "file"
  }

  object optWatch extends inox.FlagOptionDef("watch", false)
  def isWatchModeOn(using ctx: inox.Context): Boolean = ctx.options.findOptionOrDefault(optWatch)

  object optCompact extends inox.FlagOptionDef("compact", false)
  def isCompactModeOn(using ctx: inox.Context): Boolean = ctx.options.findOptionOrDefault(optCompact)

  object optExtendedSummary extends inox.FlagOptionDef("extended-summary", false)
  def isExtendedSummaryOn(using ctx: inox.Context): Boolean = ctx.options.findOptionOrDefault(optExtendedSummary)

  type Program = inox.Program { val trees: ast.Trees }

  type StainlessProgram = Program { val trees: stainless.trees.type }

  /** Including these aliases here makes default imports more natural. */
  type Identifier = inox.Identifier
  val FreshIdentifier = inox.FreshIdentifier

  extension (id: Identifier) {
    def fullName: String = id match {
      case ast.SymbolIdentifier(name) => name
      case _ => id.name
    }
  }

  extension [T <: inox.ast.Trees#Tree](tree: T) {
    def ensurePos(pos: Position): T = if (tree.getPos != NoPosition) tree else tree.setPos(pos)
  }

  object trees extends ast.Trees with inox.ast.SimpleSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      sorts: Map[Identifier, ADTSort]
    ) extends SimpleSymbols with StainlessAbstractSymbols {
      override val symbols: this.type = this
    }

    override def mkSymbols(functions: Map[Identifier, FunDef], sorts: Map[Identifier, ADTSort]): Symbols = {
      Symbols(functions, sorts)
    }

    object printer extends ast.ScalaPrinter { val trees: stainless.trees.type = stainless.trees }
  }

  val stainlessSemantics: inox.SemanticsProvider { val trees: stainless.trees.type } =
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
  given givenStainlessSemantics: stainlessSemantics.type = stainlessSemantics

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

        class DecoderImpl(override val s: stainless.trees.type,
                          override val t: trees.type) extends transformers.ConcreteTreeTransformer(s, t)
        val decoderImpl = new DecoderImpl(stainless.trees, trees)

        class ProgramEncoderImpl(override val sourceProgram: self.program.type,
                                 override val t: stainless.trees.type,
                                 override val encoder: transformer.type,
                                 override val decoder: decoderImpl.type)
          extends ProgramEncoder(t, sourceProgram, encoder, decoder)()
        val encoder = new ProgramEncoderImpl(self.program, stainless.trees, transformer, decoderImpl)

        protected def createSolver(ctx: inox.Context): inox.solvers.SolverFactory {
          val program: self.program.type
          type S <: inox.solvers.combinators.TimeoutSolver { val program: self.program.type }
        } = solvers.SolverFactory.getFromSettings(self.program, ctx)(encoder)(using self.asInstanceOf[self.program.Semantics])

        protected def createEvaluator(ctx: inox.Context): inox.evaluators.DeterministicEvaluator {
          val program: self.program.type
        } = inox.evaluators.EncodingEvaluator(self.program)(encoder)(evaluators.Evaluator(encoder.targetProgram, ctx))
      }.asInstanceOf[p.Semantics] // @nv: unfortunately required here...
    }
  }

  def topLevelErrorHandler(e: Throwable)(using ctx: inox.Context): Nothing = {
    val debugStack = ctx.reporter.debugSections.contains(frontend.DebugSectionStack)
    val isMalformedError =
      e match {
        case extraction.MalformedStainlessCode(tree, msg) =>
          ctx.reporter.error(tree.getPos, msg)
          true
        case _ => false
      }

    ctx.reporter.error(s"Stainless terminated with an error.")

    if (!debugStack && isMalformedError) System.exit(2)

    val sw = new StringWriter
    e.printStackTrace(new PrintWriter(sw))
    new PrintWriter("stainless-stack-trace.txt") { write(sw.toString); close }

    ctx.reporter.error(
      "Debug output is available in the file `stainless-stack-trace.txt`. " +
      "If the crash is caused by Stainless, you may report your issue on https://github.com/epfl-lara/stainless/issues")

    if (debugStack)
      ctx.reporter.debug(sw.toString)(using frontend.DebugSectionStack)
    else
      ctx.reporter.error("You may use --debug=stack to have the stack trace displayed in the output.")

    System.exit(2)
    ??? // unreachable
  }


  /* Parallelism utilities */

  private lazy val nParallel: Option[Int] =
    Option(System.getProperty("parallel"))
      .flatMap(p => scala.util.Try(p.toInt).toOption)

  lazy val useParallelism: Boolean = nParallel.isEmpty || nParallel.exists(_ > 1)

  private lazy val singleThreadExecutionContext: ExecutionContext =
    ExecutionContext.fromExecutor(Executors.newFixedThreadPool(1))

  private lazy val multiThreadedExecutor: java.util.concurrent.ExecutorService =
    nParallel.map(Executors.newFixedThreadPool(_)).getOrElse(ForkJoinTasks.defaultForkJoinPool)
  lazy val multiThreadedExecutionContext: ExecutionContext =
    ExecutionContext.fromExecutor(multiThreadedExecutor)

  implicit def executionContext(using ctx: inox.Context): ExecutionContext =
    if (useParallelism && ctx.reporter.debugSections.isEmpty) multiThreadedExecutionContext
    else singleThreadExecutionContext

  def shutdown(): Unit = if (useParallelism) multiThreadedExecutor.shutdown()
}
