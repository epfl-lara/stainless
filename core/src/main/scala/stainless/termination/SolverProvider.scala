/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package termination

import scala.concurrent.duration._

import scala.language.existentials

trait SolverProvider { self =>
  val checker: ProcessingPipeline
  import checker.program._
  import checker.program.trees._
  import checker.program.symbols._

  val encoder: ast.TreeTransformer {
    val s: trees.type
    val t: stainless.trees.type
  }

  private var transformers: inox.ast.SymbolTransformer { val s: trees.type; val t: trees.type } =
    new inox.ast.SymbolTransformer {
      val s: trees.type = trees
      val t: trees.type = trees

      def transform(syms: Symbols): Symbols = syms
    }

  private[termination] def registerTransformer(
    transformer: inox.ast.SymbolTransformer { val s: trees.type; val t: trees.type }
  ): Unit = transformers = transformers andThen transformer

  private implicit val semanticsProvider: inox.SemanticsProvider { val trees: checker.program.trees.type } =
    encodingSemantics(trees)(encoder)


  private val cache = new inox.utils.LruCache[
    inox.ast.SymbolTransformer,
    inox.solvers.SolverFactory { val program: Program { val trees: checker.program.trees.type } }
  ](5)

  private[termination] def clearSolvers(): Unit = cache.clear()

  private def solverFactory(transformer: inox.ast.SymbolTransformer { val s: trees.type; val t: trees.type }) =
    cache.cached(transformer, {
      val timer = ctx.timers.termination.encoding.start()
      val transformEncoder = inox.ast.ProgramEncoder(checker.program)(transformer)
      val p: transformEncoder.targetProgram.type = transformEncoder.targetProgram

      object programEncoder extends {
        val sourceProgram: p.type = p
        val t: stainless.trees.type = stainless.trees
      } with inox.ast.ProgramEncoder {
        val encoder = self.encoder
        object decoder extends ast.TreeTransformer {
          val s: stainless.trees.type = stainless.trees
          val t: trees.type = trees
        }
      }

      val timeout = ctx.options.findOption(inox.optTimeout) match {
        case Some(to) => to / 100
        case None => 2.5.seconds
      }

      val allOptions = checker.options ++ Seq(
        inox.solvers.optSilentErrors(true),
        inox.solvers.optCheckModels(true)
      )

      val factory = solvers.SolverFactory
        .getFromSettings(p, allOptions)(programEncoder)(p.getSemantics)
        .withTimeout(timeout)

      timer.stop()
      factory
    })

  private def solverAPI(transformer: inox.ast.SymbolTransformer { val s: trees.type; val t: trees.type }) = {
    inox.solvers.SimpleSolverAPI(solverFactory(transformer))
  }

  def getAPI: inox.solvers.SimpleSolverAPI {
    val program: inox.Program { val trees: checker.program.trees.type }
  } = solverAPI(transformers)

  def getAPI(t: inox.ast.SymbolTransformer { val s: trees.type; val t: trees.type }): inox.solvers.SimpleSolverAPI {
    val program: inox.Program { val trees: checker.program.trees.type }
  } = solverAPI(transformers andThen t)
}
