/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package termination

import inox.transformers._

import scala.concurrent.duration._

trait SolverProvider { self =>
  val checker: ProcessingPipeline

  import checker._
  import context.{given, _}
  import program._
  import program.trees._
  import program.symbols.{given, _}
  import inox.solvers.factoryToTimeoutableFactory

  val encoder: TreeTransformer {
    val s: trees.type
    val t: stainless.trees.type
  }

  private var transformers: SymbolTransformer { val s: trees.type; val t: trees.type } = new TransformersImpl()

  private[termination] def registerTransformer(
      transformer: SymbolTransformer { val s: trees.type; val t: trees.type }
  ): Unit = transformers = transformers andThen transformer

  private val semanticsProvider: inox.SemanticsProvider { val trees: checker.program.trees.type } =
    encodingSemantics(trees)(encoder)
  private given givenSemanticsProvider: semanticsProvider.type = semanticsProvider

  private def solverFactory(transformer: SymbolTransformer { val s: trees.type; val t: trees.type }) =
    context.timers.termination.encoding.run {
      val transformEncoder = ProgramEncoder(checker.program)(transformer)
      val p: transformEncoder.targetProgram.type = transformEncoder.targetProgram

      class DecoderImpl(override val s: stainless.trees.type,
                        override val t: trees.type) extends TreeTransformer
      class ProgramEncoderImpl(override val t: stainless.trees.type,
                               override val sourceProgram: p.type,
                               override val encoder: self.encoder.type,
                               override val decoder: DecoderImpl)
        extends ProgramEncoder(t, sourceProgram, encoder, decoder)()
      val programEncoder = new ProgramEncoderImpl(stainless.trees, p, self.encoder, new DecoderImpl(stainless.trees, trees))

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
        )(programEncoder)(using p.getSemantics)
        .withTimeout(timeout)
    }

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

  private class TransformersImpl private(override val s: trees.type, override val t: trees.type) extends SymbolTransformer {
    def this() = this(trees, trees)

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
}
