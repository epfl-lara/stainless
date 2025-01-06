/* Copyright 2009-2021 EPFL, Lausanne */

package stainless

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
    "UserFiltering"             -> "Remove all the library functions not used by the user",
    "Preprocessing"             -> "A preprocessing phase before the pipeline",
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
    "ExceptionLifting"          -> "Removes all throw statements, and replaces them with an assertion with false condition",
    "FieldAccessors"            -> "Inline field accessors of concrete classes",
    "EffectElaboration"         -> "Transform all side-effectful operations into mutable map updates",
    "AntiAliasing"              -> "Rewrite field and array mutations",
    "ReturnElimination"         -> "Eliminate `return` expressions",
    "ImperativeCodeElimination" -> "Eliminate while loops and assignments",
    "ImperativeCleanup"         -> "Cleanup after imperative transformations",
    "InvariantInitialization"   -> "Add initialization for classes where all fields have default values",
    "AdtSpecialization"         -> "Specialize classes into ADTs (when possible)",
    "RefinementLifting"         -> "Lift simple refinements to contracts",
    "TypeEncoding"              -> "Encode non-ADT types",
    "FunctionClosure"           -> "Lift inner functions",
    "FunctionSpecialization"    -> "Specialize functions",
    "UnfoldOpaque"              -> "Injects equality assumption with inlined call for calls wrapped in unfold keyword",
    "CallSiteInline"            -> "Call-side inline for calls wrapped in inline keyword",
    "ChooseInjector"            -> "Insert chooses where necessary",
    "ChooseEncoder"             -> "Encodes chooses as functions",
    "FunctionInlining"          -> "Transitively inline marked functions",
    "LeonInlining"              -> "Transitively inline marked functions (closer to what Leon did)",
    "TraceInductElimination"    -> "Expand @traceInduct",
    "SizedADTExtraction"        -> "Transform calls to 'indexedAt' to the 'SizedADT' tree",
    "InductElimination"         -> "Replace @induct annotation by explicit recursion",
    "MeasureInference"          -> "Infer and inject measures in recursive functions",
    "PartialEvaluation"         -> "Partially evaluate marked function calls",
    "AssertionInjector"         -> "Insert assertions which verify array accesses, casts, division by zero, etc.",

    "ComputeDependencies"       -> "(GenC) Compute the dependencies of a given definition",
    "ComputeFunCtx"             -> "(GenC) Compute the context of each given function definition",
    "GhostElimination"          -> "(GenC) Remove ghost code",
    "Scala2IR"                  -> "(GenC) Convert the Stainless AST into GenC's IR",
    "StructInlining"            -> "(GenC) Inline structs which have just one member",
    "Normalisation"             -> "(GenC) Normalise IR to match the C execution model",
    "Lifting"                   -> "(GenC) Lift class types to their hierarchy top class",
    "Referencing"               -> "(GenC) Add 'referencing' to the input LIR program to produce a RIR program",
    "IR2C"                      -> "(GenC) From IR to C",
  )

  // The tag used when printing progress about which phase is currently running
  case object PhaseExtractionTag

  val phaseNames: Set[String] = phases.map(_._1).toSet

  /** Unifies all stainless tree definitions */
  trait Trees extends ast.Trees { self =>
    case object Uncached extends Flag("uncached", Seq.empty)

    override def getDeconstructor(that: inox.ast.Trees): inox.ast.TreeDeconstructor { val s: self.type; val t: that.type } = that match {
      case tree: (Trees & that.type) => // The `& that.type` trick allows to convince scala that `tree` and `that` are actually equal...
        class DeconstructorImpl(override val s: self.type, override val t: tree.type & that.type) extends ConcreteTreeDeconstructor(s, t)
        new DeconstructorImpl(self, tree)

      case _ => super.getDeconstructor(that)
    }

    override val exprOps: ExprOps { val trees: self.type } = {
      class ExprOpsImpl(override val trees: self.type) extends ExprOps(trees)
      new ExprOpsImpl(self)
    }
  }

  /** Unifies all stainless tree printers */
  trait Printer extends ast.Printer

  /** Unifies all stainless tree extractors */
  trait TreeDeconstructor extends ast.TreeDeconstructor {
    protected val s: Trees
    protected val t: Trees
  }

  class ConcreteTreeDeconstructor(override val s: Trees, override val t: Trees) extends TreeDeconstructor

  /** Unifies all stainless expression operations */
  class ExprOps(override val trees: Trees) extends ast.ExprOps(trees)

  object trees extends Trees with inox.ast.SimpleSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      sorts: Map[Identifier, ADTSort]
    ) extends SimpleSymbols with StainlessAbstractSymbols {
      override val symbols: this.type = this
    }

    override def mkSymbols(functions: Map[Identifier, FunDef], sorts: Map[Identifier, ADTSort]): Symbols = {
      Symbols(functions, sorts)
    }

    object printer extends Printer { val trees: extraction.trees.type = extraction.trees }
  }

  case class ExtractionFailed() extends Exception("Extraction failed")
  case class MalformedStainlessCode(tree: inox.ast.Trees#Tree, msg: String)
    extends Exception(msg)

  def pipeline(using inox.Context): StainlessPipeline = {
    xlang.extractor        `andThen`
    innerclasses.extractor `andThen`
    methods.extractor      `andThen`
    throwing.extractor     `andThen`
    imperative.extractor   `andThen`
    oo.extractor           `andThen`
    innerfuns.extractor    `andThen`
    inlining.extractor     `andThen`
    trace.extractor        `andThen`
    termination.extractor
  }

  private def completeSymbols(symbols: trees.Symbols)(to: ast.Trees): to.Symbols = {
    class CompleteSymbolsImpl(override val s: extraction.trees.type, override val t: to.type) extends CheckingTransformer
    symbols.transform(new CompleteSymbolsImpl(extraction.trees, to))
  }

  def completer(to: ast.Trees)(using inox.Context) = {
    class CompleterImpl(override val s: extraction.trees.type,
                        override val t: to.type)
                       (using override val context: inox.Context)
      extends ExtractionPipeline { self =>

      override def invalidate(id: Identifier): Unit = ()
      override def extract(symbols: s.Symbols): (t.Symbols, ExtractionSummary) =
        (completeSymbols(symbols)(to), ExtractionSummary.NoSummary)
    }
    new CompleterImpl(extraction.trees, to)
  }

  type StainlessPipeline = ExtractionPipeline {
    val s: xlang.trees.type
    val t: trees.type
  }

  val extractionSemantics: inox.SemanticsProvider { val trees: extraction.trees.type } = {
    getSemantics(extraction.trees)(syms => syms)
  }

  given givenExtractionSemantics: extractionSemantics.type = extractionSemantics

  def phaseSemantics(tr: ast.Trees)
                    (pipeline: ExtractionPipeline { val s: tr.type; val t: extraction.trees.type }):
                    inox.SemanticsProvider { val trees: tr.type } = {
    getSemantics(tr)(syms => pipeline.extract(syms)._1)
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

        private val targetSymbols = completeSymbols(processSymbols(symbols))(stainless.trees)
        private val targetProgram = inox.Program(stainless.trees)(targetSymbols)

        private class ProgramEncoderImpl(override val sourceProgram: self.program.type,
                                         override val targetProgram: self.targetProgram.type )
          extends inox.transformers.ProgramTransformer {

          class EncoderImpl(override val s: trees.type, override val t: stainless.trees.type)
            extends transformers.ConcreteTreeTransformer(s, t)
          override val encoder = new EncoderImpl(trees, stainless.trees)

          class DecoderImpl(override val s: stainless.trees.type, override val t: trees.type)
            extends transformers.ConcreteTreeTransformer(s, t)
          override val decoder = new DecoderImpl(stainless.trees, trees)
        }
        private val encoder = new ProgramEncoderImpl(self.program, self.targetProgram)

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
