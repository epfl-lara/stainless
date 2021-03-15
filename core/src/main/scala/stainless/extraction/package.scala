/* Copyright 2009-2021 EPFL, Lausanne */

package stainless

import scala.language.existentials

/** Provides definitions for a hierarchy of languages above stainless,
  * topped by xlang, which is the extended input language of stainless.
  *
  * The traits [[extraction.Trees]], [[extraction.TreeDeconstructor]]
  * and [[extraction.ExprOps]] (defined in the [[extraction]] package
  * object) provide the unification point of all different stainless tree
  * types that can appear once extraction and pre-processing has finished.
  *
  * The hierarhcy is
  *   extraction < inlining < innerfuns < imperative < oo < throwing < methods < xlang
  *
  * Inlining adds support for function inlining.
  * Innerfuns adds inner functions.
  * Imperative adds imperative features.
  * OO adds object-oriented features.
  * Throwing handles exception lifting.
  * Methods takes care of method lifting.
  * xlang adds imports and module structure.
  */
package object extraction {

  val phases: Seq[(String, String)] = Seq(
    "PartialFunctions"          -> "Lift partial function preconditions",
    "XlangLowering"             -> "Lowering phase at the end of xlang phases",
    "InnerClasses"              -> "Lift inner classes",
    "Laws"                      -> "Rewrite laws as abstract functions with contracts",
    "SuperInvariants"           -> "Ensure super class invariant cannot be weakened in subclasses",
    "SuperCalls"                -> "Resolve super-function calls",
    "Sealing"                   -> "Seal every class and add mutable flags",
    "MethodLifting"             -> "Lift methods into dispatching functions",
    "MergeInvariants"           -> "Merge all class invariants into a single method",
    "ValueClasses"              -> "Erase value classes",
    "FieldAccessors"            -> "Inline field accessors of concrete classes",
    "AntiAliasing"              -> "Rewrite field and array mutations",
    "ReturnElimination"         -> "Eliminate `return` expressions",
    "ImperativeCodeElimination" -> "Eliminate while loops and assignments",
    "ImperativeCleanup"         -> "Cleanup after imperative transformations",
    "AdtSpecialization"         -> "Specialize classes into ADTs (when possible)",
    "RefinementLifting"         -> "Lift simple refinements to contracts",
    "TypeEncoding"              -> "Encode non-ADT types",
    "FunctionClosure"           -> "Lift inner functions",
    "FunctionSpecialization"    -> "Specialize functions",
    "FunctionInlining"          -> "Transitively inline marked functions",
    "LeonInlining"              -> "Transitively inline marked functions (closer to what Leon did)",
    "Trace"                     -> "Apply the traceInduct tactic during verification of the annotated function.",
    "SizedADTExtraction"        -> "Transforms calls to 'indexedAt' to the 'SizedADT' tree",
    "InductElimination"         -> "Replace @induct annotation by explicit recursion",
    "SizeInjection"             -> "Injects a size function for each ADT",
    "MeasureInference"          -> "Infer and inject measures in recursive functions",
    "PartialEvaluation"         -> "Partially evaluate marked function calls",
    "AssertionInjector"         -> "Insert assertions which verify array accesses, casts, division by zero, etc.",
    "ChooseInjector"            -> "Insert chooses where necessary",
  )

  val phaseNames: Set[String] = phases.map(_._1).toSet

  /** Unifies all stainless tree definitions */
  trait Trees extends ast.Trees { self =>
    case object Uncached extends Flag("uncached", Seq.empty)

    override def getDeconstructor(that: inox.ast.Trees): inox.ast.TreeDeconstructor { val s: self.type; val t: that.type } = that match {
      case tree: Trees => new TreeDeconstructor {
        protected val s: self.type = self
        protected val t: tree.type = tree
      }.asInstanceOf[TreeDeconstructor { val s: self.type; val t: that.type }]

      case _ => super.getDeconstructor(that)
    }

    override val exprOps: ExprOps { val trees: self.type } = new {
      protected val trees: self.type = self
    } with ExprOps
  }

  /** Unifies all stainless tree printers */
  trait Printer extends ast.Printer

  /** Unifies all stainless tree extractors */
  trait TreeDeconstructor extends ast.TreeDeconstructor {
    protected val s: Trees
    protected val t: Trees
  }

  /** Unifies all stainless expression operations */
  trait ExprOps extends ast.ExprOps

  object trees extends Trees with inox.ast.SimpleSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      sorts: Map[Identifier, ADTSort]
    ) extends SimpleSymbols with AbstractSymbols

    object printer extends Printer { val trees: extraction.trees.type = extraction.trees }
  }

  case class MalformedStainlessCode(tree: inox.ast.Trees#Tree, msg: String)
    extends Exception(msg)

  def pipeline(implicit ctx: inox.Context): StainlessPipeline = {
    xlang.extractor        andThen
    innerclasses.extractor andThen
    methods.extractor      andThen
    throwing.extractor     andThen
    imperative.extractor   andThen
    oo.extractor           andThen
    innerfuns.extractor    andThen
    inlining.extractor     andThen
    trace.extractor        andThen
    termination.extractor
  }

  private[this] def completeSymbols(symbols: trees.Symbols)(to: ast.Trees): to.Symbols = {
    symbols.transform(new CheckingTransformer {
      override val s: extraction.trees.type = extraction.trees
      override val t: to.type = to
    })
  }

  def completer(to: ast.Trees)(implicit ctx: inox.Context) = new ExtractionPipeline { self =>
    override val s: extraction.trees.type = extraction.trees
    override val t: to.type = to
    override val context = ctx

    override def invalidate(id: Identifier): Unit = ()
    override def extract(symbols: s.Symbols): t.Symbols = completeSymbols(symbols)(to)
  }

  type StainlessPipeline = ExtractionPipeline {
    val s: xlang.trees.type
    val t: trees.type
  }

  implicit val extractionSemantics: inox.SemanticsProvider { val trees: extraction.trees.type } = {
    getSemantics(extraction.trees)(syms => syms)
  }

  def phaseSemantics(tr: ast.Trees)
                    (pipeline: ExtractionPipeline { val s: tr.type; val t: extraction.trees.type }):
                    inox.SemanticsProvider { val trees: tr.type } = {
    getSemantics(tr)(syms => pipeline.extract(syms))
  }

  def getSemantics(tr: ast.Trees)(processSymbols: tr.Symbols => extraction.trees.Symbols):
                   inox.SemanticsProvider { val trees: tr.type } =
    new inox.SemanticsProvider {
      val trees: tr.type = tr

      def getSemantics(p: inox.Program { val trees: tr.type }): p.Semantics = new inox.Semantics { self =>
        val trees: p.trees.type = p.trees
        val symbols: p.symbols.type = p.symbols
        val program: Program { val trees: p.trees.type; val symbols: p.symbols.type } =
          p.asInstanceOf[Program { val trees: p.trees.type; val symbols: p.symbols.type }]

        private[this] val targetSymbols = completeSymbols(processSymbols(symbols))(stainless.trees)
        private[this] val targetProgram = inox.Program(stainless.trees)(targetSymbols)

        private object encoder extends inox.transformers.ProgramTransformer {
          override val sourceProgram: self.program.type = self.program
          override val targetProgram = self.targetProgram

          override object encoder extends transformers.TreeTransformer {
            val s: trees.type = trees
            val t: stainless.trees.type = stainless.trees
          }

          override object decoder extends transformers.TreeTransformer {
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
