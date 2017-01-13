/* Copyright 2009-2016 EPFL, Lausanne */

package object stainless {

  type Program = inox.Program { val trees: ast.Trees }

  type StainlessProgram = Program { val trees: stainless.trees.type }

  /** Including these aliases here makes default imports more natural. */
  type Identifier = inox.Identifier
  val FreshIdentifier = inox.FreshIdentifier

  object trees extends ast.Trees with inox.ast.SimpleSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      adts: Map[Identifier, ADTDefinition]
    ) extends SimpleSymbols with AbstractSymbols
  }

  // @nv: as for Inox, we have to work around the type system a bit here...

  trait SemanticsProvider {
    val program: Program
    def getSemantics(encoder: inox.ast.ProgramTransformer {
      val sourceProgram: program.type
      val targetProgram: inox.Program { val trees: stainless.trees.type }
    }): program.Semantics

    def getSemantics(implicit ev: program.type <:< StainlessProgram): program.Semantics = {
      val p: inox.Program { val trees: stainless.trees.type } = ev(program)
      val encoder = inox.ast.ProgramEncoder.empty(p).asInstanceOf[inox.ast.ProgramTransformer {
        val sourceProgram: program.type
        val targetProgram: p.type
      }]
      getSemantics(encoder).asInstanceOf[program.Semantics]
    }
  }

  implicit def stainlessSemantics(p: Program): SemanticsProvider { val program: p.type } = new SemanticsProvider {
    val program: p.type = p
    def getSemantics(encoder: inox.ast.ProgramTransformer {
      val sourceProgram: p.type
      val targetProgram: inox.Program { val trees: stainless.trees.type }
    }): p.Semantics = new inox.Semantics { self =>
      val trees: p.trees.type = p.trees
      val symbols: p.symbols.type = p.symbols
      val program: Program { val trees: p.trees.type; val symbols: p.symbols.type } = p.asInstanceOf[Program {
        val trees: p.trees.type
        val symbols: p.symbols.type
      }]

      private val selfEncoder = encoder.asInstanceOf[inox.ast.ProgramTransformer {
        val sourceProgram: self.program.type
        val targetProgram: inox.Program { val trees: stainless.trees.type }
      }]

      def getSolver(opts: inox.Options): inox.solvers.SolverFactory {
        val program: self.program.type
        type S <: inox.solvers.combinators.TimeoutSolver { val program: self.program.type }
      } = solvers.SolverFactory.getFromSettings(self.program, opts)(selfEncoder)(this.asInstanceOf[self.program.Semantics])

      def getEvaluator(opts: inox.Options): inox.evaluators.DeterministicEvaluator { val program: self.program.type } = {
        inox.evaluators.EncodingEvaluator(self.program)(selfEncoder)(evaluators.Evaluator(selfEncoder.targetProgram, opts))
      }
    }.asInstanceOf[p.Semantics] // @nv: unfortunately required here...
  }
}
