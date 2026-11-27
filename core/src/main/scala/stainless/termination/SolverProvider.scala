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
  ): Unit = transformers = transformers `andThen` transformer

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

      // With a resource limit for each solver, a query is bounded by that limit and by an unrolling
      // bound, which don't depend on the load of the machine. The timeout then only bounds the time
      // outside of the solver. Otherwise, a query gets a small part of the timeout.
      val (timeout, limits) =
        if (SolverProvider.resourceLimited(options)) {
          import inox.solvers.smtlib.{optZ3Rlimit, optCVC5Rlimit}
          val bound = inox.solvers.unrolling.optUnrollBound(options.findOptionOrDefault(optTerminationUnrollBound))
          val rlimit = options.findOptionOrDefault(optTerminationRlimit)
          def lower(opt: inox.IntOptionDef) = {
            val current = options.findOptionOrDefault(opt)
            opt(if (current > 0) current min rlimit else current)
          }
          (options.findOption(inox.optTimeout), Seq(bound, lower(optZ3Rlimit), lower(optCVC5Rlimit)))
        } else {
          (Some(options.findOption(inox.optTimeout).map(_ / 100).getOrElse(2.5.seconds)), Seq())
        }

      val factory = solvers.SolverFactory
        .getFromSettings(
          p,
          context.withOpts(Seq(
            inox.solvers.optSilentErrors(true),
            inox.solvers.optCheckModels(true)
          ) ++ limits*)
        )(programEncoder)(using p.getSemantics)
      timeout match {
        case Some(to) => factory.withTimeout(to)
        case None => factory
      }
    }

  private def solverAPI(transformer: SymbolTransformer { val s: trees.type; val t: trees.type }) = {
    inox.solvers.SimpleSolverAPI(solverFactory(transformer))
  }

  def getAPI: inox.solvers.SimpleSolverAPI {
    val program: inox.Program { val trees: checker.program.trees.type }
  } = solverAPI(transformers)

  def getAPI(t: SymbolTransformer { val s: trees.type; val t: trees.type }): inox.solvers.SimpleSolverAPI {
    val program: inox.Program { val trees: checker.program.trees.type }
  } = solverAPI(transformers `andThen` t)

  /** A solver for the queries that prove the termination of `fds`, where their postconditions don't
    * hold yet: they only hold of calls that return, and these queries are about calls that may not.
    * A call on arguments that don't decrease could otherwise rely on its own postcondition, which
    * holds vacuously when it diverges or when the postcondition is false. */
  def getAPIWithoutPosts(fds: Set[FunDef]): inox.solvers.SimpleSolverAPI {
    val program: inox.Program { val trees: checker.program.trees.type }
  } = getAPI(new ConcreteIdentitySymbolTransformer {
    override def transform(syms: Symbols): Symbols = {
      val transformed = super.transform(syms)
      transformed.withFunctions(fds.toSeq.flatMap(fd => transformed.lookupFunction(fd.id)).map { fd =>
        fd.copy(fullBody = exprOps.withPostcondition(fd.fullBody, None)).copiedFrom(fd)
      })
    }
  })

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

object SolverProvider {
  /** Whether each selected solver has a resource limit for its checks. */
  def resourceLimited(options: inox.Options): Boolean = {
    import inox.solvers.smtlib.{optZ3Rlimit, optCVC5Rlimit}
    def limited(opt: inox.IntOptionDef) = options.findOptionOrDefault(opt) > 0
    val solvers = options.findOptionOrDefault(inox.optSelectedSolvers)
    solvers.nonEmpty && solvers.forall { name =>
      if (name == "smt-cvc5") limited(optCVC5Rlimit)
      else if (name.contains("z3")) limited(optZ3Rlimit)
      else false
    }
  }
}
