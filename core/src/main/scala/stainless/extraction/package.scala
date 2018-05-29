/* Copyright 2009-2018 EPFL, Lausanne */

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

  /** Unifies all stainless tree definitions */
  trait Trees extends ast.Trees with termination.Trees { self =>
    override def getDeconstructor(that: inox.ast.Trees): inox.ast.TreeDeconstructor { val s: self.type; val t: that.type } = that match {
      case tree: Trees => new TreeDeconstructor {
        protected val s: self.type = self
        protected val t: tree.type = tree
      }.asInstanceOf[TreeDeconstructor { val s: self.type; val t: that.type }]

      case _ => super.getDeconstructor(that)
    }

    object Uncached extends Flag("uncached", Seq())

    override val exprOps: ExprOps { val trees: self.type } = new {
      protected val trees: self.type = self
    } with ExprOps
  }

  /** Unifies all stainless tree printers */
  trait Printer extends ast.Printer with termination.Printer

  /** Unifies all stainless tree extractors */
  trait TreeDeconstructor extends ast.TreeDeconstructor with termination.TreeDeconstructor {
    protected val s: Trees
    protected val t: Trees

    override def deconstruct(flag: s.Flag): DeconstructedFlag = flag match {
      case s.Uncached => (Seq(), Seq(), Seq(), (_, _, _) => t.Uncached)
      case _ => super.deconstruct(flag)
    }
  }

  /** Unifies all stainless expression operations */
  trait ExprOps extends ast.ExprOps with termination.ExprOps

  object trees extends Trees with inox.ast.SimpleSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      sorts: Map[Identifier, ADTSort]
    ) extends SimpleSymbols with AbstractSymbols

    object printer extends Printer { val trees: extraction.trees.type = extraction.trees }
  }

  case class MissformedStainlessCode(tree: inox.ast.Trees#Tree, msg: String)
    extends Exception(msg)

  def pipeline(implicit ctx: inox.Context) = {
    xlang.extractor      andThen
    methods.extractor    andThen
    throwing.extractor   andThen
    oo.extractor         andThen
    imperative.extractor andThen
    innerfuns.extractor  andThen
    inlining.extractor
  }

  private[this] def completeSymbols(symbols: trees.Symbols)(to: ast.Trees): to.Symbols = {
    object checker extends CheckingTransformer {
      override val s: extraction.trees.type = extraction.trees
      override val t: to.type = to
    }

    import extraction.trees._
    val newFunctions = symbols.functions.values.toSeq.map(fd => fd.copy(flags = fd.flags filterNot (_ == Uncached)))
    val newSorts = symbols.sorts.values.toSeq.map(sort => sort.copy(flags = sort.flags filterNot (_ == Uncached)))
    NoSymbols.withFunctions(newFunctions).withSorts(newSorts).transform(checker)
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

  implicit val extractionSemantics: inox.SemanticsProvider { val trees: extraction.trees.type } =
    new inox.SemanticsProvider {
      val trees: extraction.trees.type = extraction.trees

      def getSemantics(p: inox.Program { val trees: extraction.trees.type }): p.Semantics = new inox.Semantics { self =>
        val trees: p.trees.type = p.trees
        val symbols: p.symbols.type = p.symbols
        val program: Program { val trees: p.trees.type; val symbols: p.symbols.type } =
          p.asInstanceOf[Program { val trees: p.trees.type; val symbols: p.symbols.type }]

        private[this] val targetProgram = inox.Program(stainless.trees)(completeSymbols(symbols)(stainless.trees))

        private object encoder extends inox.ast.ProgramTransformer {
          override val sourceProgram: self.program.type = self.program
          override val targetProgram = self.targetProgram

          override object encoder extends ast.TreeTransformer {
            val s: trees.type = trees
            val t: stainless.trees.type = stainless.trees
          }

          override object decoder extends ast.TreeTransformer {
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
