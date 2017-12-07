/* Copyright 2009-2016 EPFL, Lausanne */

package object stainless {

  object DebugSectionExtraction extends inox.DebugSection("extraction")

  object optJson extends inox.OptionDef[String] {
    val name = "json"
    val default = "report.json"
    val parser = inox.OptionParsers.stringParser
    val usageRhs = "file"
  }

  object optWatch extends inox.FlagOptionDef("watch", false)
  def isWatchModeOn(implicit ctx: inox.Context) = ctx.options.findOptionOrDefault(optWatch)

  type Program = inox.Program { val trees: ast.Trees }

  type StainlessProgram = Program { val trees: stainless.trees.type }

  /** Including these aliases here makes default imports more natural. */
  type Identifier = inox.Identifier
  val FreshIdentifier = inox.FreshIdentifier

  implicit class IdentifierFromSymbol(id: Identifier) {
    def fullName: String = id match {
      case ast.SymbolIdentifier(name) => name
      case _ => id.name
    }
  }

  object trees extends ast.Trees with inox.ast.SimpleSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      adts: Map[Identifier, ADTDefinition]
    ) extends SimpleSymbols with AbstractSymbols

    object printer extends ast.Printer { val trees: stainless.trees.type = stainless.trees }
  }

  implicit val stainlessSemantics: inox.SemanticsProvider { val trees: stainless.trees.type } = new inox.SemanticsProvider {
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
                       (transformer: inox.ast.TreeTransformer { val s: ts.type; val t: stainless.trees.type }):
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
        } with inox.ast.ProgramEncoder {
          val encoder = transformer
          object decoder extends ast.TreeTransformer {
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
}
