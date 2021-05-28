/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package termination

import inox.transformers._

import scala.concurrent.duration._

import scala.language.existentials

trait SolverProvider { self =>
  val checker: ProcessingPipeline

  import checker._
  import context._
  import program._
  import program.trees._
  import program.symbols._

  val encoder: TreeTransformer {
    val s: trees.type
    val t: stainless.trees.type
  }

  private var transformers: SymbolTransformer { val s: trees.type; val t: trees.type } =
    new SymbolTransformer {
      val s: trees.type = trees
      val t: trees.type = trees

      def transform(syms: Symbols): Symbols = {
        val newSorts = symbols.sorts.values.toSeq
        val newFunctions = symbols.functions.values.toSeq.map(fd =>
          fd.copy(flags = fd.flags.filter {
            case Uncached => false
            case _        => true
          }).copiedFrom(fd)
        )

        NoSymbols.withSorts(newSorts).withFunctions(newFunctions)
      }
    }

  private[termination] def registerTransformer(
      transformer: SymbolTransformer { val s: trees.type; val t: trees.type }
  ): Unit = transformers = transformers andThen transformer

  private implicit val semanticsProvider: inox.SemanticsProvider { val trees: checker.program.trees.type } =
    encodingSemantics(trees)(encoder)

  private def solverFactory(transformer: SymbolTransformer { val s: trees.type; val t: trees.type }) =
    (timers.termination.encoding.run {
      val transformEncoder = ProgramEncoder(checker.program)(transformer)
      val p: transformEncoder.targetProgram.type = transformEncoder.targetProgram

      object programEncoder extends {
        val sourceProgram: p.type = p
        val t: stainless.trees.type = stainless.trees
      } with ProgramEncoder {
        val encoder = self.encoder
        object decoder extends TreeTransformer {
          val s: stainless.trees.type = stainless.trees
          val t: trees.type = trees
        }
      }

      val timeout = options.findOption(inox.optTimeout) match {
        case Some(to) => to / 100
        case None     => 2.5.seconds
      }

      solvers.SolverFactory
        .getFromSettings(
          p,
          context.withOpts(
            inox.solvers.optSilentErrors(true),
            inox.solvers.optCheckModels(true)
          )
        )(programEncoder)(p.getSemantics)
        .withTimeout(timeout)
    })

  private def solverAPI(transformer: SymbolTransformer { val s: trees.type; val t: trees.type }) = {
    inox.solvers.SimpleSolverAPI(solverFactory(transformer))
  }

  def getAPI: inox.solvers.SimpleSolverAPI {
    val program: inox.Program { val trees: checker.program.trees.type }
  } = solverAPI(transformers)

  def getAPI(t: SymbolTransformer { val s: trees.type; val t: trees.type }): inox.solvers.SimpleSolverAPI {
    val program: inox.Program { val trees: checker.program.trees.type }
  } = solverAPI(transformers andThen t)

  def apiTransform(s: Symbols) = transformers.transform(s)
}
