/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package frontends.scalac

import ast.SymbolIdentifier
import frontend.{ Frontend, FrontendFactory, CallBack }

import scala.tools.nsc.{ Global, Settings => NSCSettings, CompilerCommand }
import scala.reflect.internal.Positions

import scala.collection.mutable.{ Map => MutableMap }

object SymbolMapping {
  def getPath(sym: Global#Symbol): String =
    sym.ownerChain.reverse map { s => s"${s.name}#${kind(s)}" } mkString "."

  def empty = new SymbolMapping()

  /**
   * To avoid suffering from changes in symbols' id, we generate a more stable
   * kind to disambiguate symbols. This allows --watch to not be fooled by the
   * insertion/deletion of symbols (e.g. new top level classes or methods).
   */
  private def kind(sym: Global#Symbol): Int = {
    if (sym.isPackageClass) 0
    else if (sym.isModule) 1
    else if (sym.isModuleClass) 2
    else if (sym.isClass) 3
    else if (sym.isMethod) 4
    else if (sym.isType) 5
    else if (sym.isTerm) {
      // Many things are terms... Fallback to its id, but negate it to be unambiguous.
      val id = -sym.id
      assert(id < 0)
      id
    } else ???
  }
}

class SymbolMapping {
  import SymbolMapping.getPath

  /** Get the identifier associated with the given [[sym]], creating a new one if needed. */
  def fetch(sym: Global#Symbol): SymbolIdentifier = s2i.getOrElseUpdate(getPath(sym), {
    val top = if (sym.overrideChain.nonEmpty) sym.overrideChain.last else sym
    val symbol = s2s.getOrElseUpdate(top, {
      val name = sym.fullName.toString.trim
      ast.Symbol(if (name endsWith "$") name.init else name)
    })

    SymbolIdentifier(symbol)
  })

  /** Get the identifier for the class invariant of [[sym]]. */
  def fetchInvIdForClass(sym: Global#Symbol): SymbolIdentifier = invs.getOrElseUpdate(fetch(sym), {
    SymbolIdentifier(invSymbol)
  })

  /** Mapping from [[Global#Symbol]] (or rather: its path) and the stainless identifier. */
  private val s2i = MutableMap[String, SymbolIdentifier]()

  /** Mapping useful to use the same top symbol mapping. */
  private val s2s = MutableMap[Global#Symbol, ast.Symbol]()

  /** Mapping for class invariants: class' id -> inv's id. */
  private val invs = MutableMap[SymbolIdentifier, SymbolIdentifier]()
  private val invSymbol = stainless.ast.Symbol("inv")

}

class ScalaCompiler(settings: NSCSettings, ctx: inox.Context, callback: CallBack, cache: SymbolMapping)
  extends Global(settings, new SimpleReporter(settings, ctx.reporter))
     with Positions {

  object stainlessExtraction extends {
    val global: ScalaCompiler.this.type = ScalaCompiler.this
    val runsAfter = List[String]("refchecks")
    val runsRightAfter = None
    val ctx = ScalaCompiler.this.ctx
    val callback = ScalaCompiler.this.callback
    val cache = ScalaCompiler.this.cache
  } with StainlessExtraction

  override protected def computeInternalPhases() : Unit = {
    val phs = List(
      syntaxAnalyzer          -> "parse source into ASTs, perform simple desugaring",
      analyzer.namerFactory   -> "resolve names, attach symbols to named trees",
      analyzer.packageObjects -> "load package objects",
      analyzer.typerFactory   -> "the meat and potatoes: type the trees",
      patmat                  -> "translate match expressions",
      superAccessors          -> "add super accessors in traits and nested classes",
      extensionMethods        -> "add extension methods for inline classes",
      pickler                 -> "serialize symbol tables",
      refChecks               -> "reference/override checking, translate nested objects",
      stainlessExtraction     -> "extracts stainless trees out of scala trees"
      // TODO drop in replacement? add next phases, plus last phase to report VC results
    )
    phs foreach { phasesSet += _._1 }
  }

  class Run extends super.Run {
    override def progress(current: Int, total: Int) {
      ctx.reporter.onCompilerProgress(current, total)
    }
  }
}

object ScalaCompiler {

  /** Complying with [[frontend]]'s interface */
  class Factory(
    override val extraCompilerArguments: Seq[String],
    override val libraryFiles: Seq[String]
  ) extends FrontendFactory {

    override def apply(ctx: inox.Context, compilerArgs: Seq[String], callback: CallBack): Frontend = {

      val args = allCompilerArguments(compilerArgs)
      val settings = buildSettings(ctx)
      val files = getFiles(args, ctx, settings)

      val cache = SymbolMapping.empty


      // Implement an interface compatible with the generic frontend.
      // If an exception is thrown from within the compiler, it is rethrown upon stopping or joining.
      // TODO refactor code, maybe, in frontend package if the same code is required for dotty/other frontends
      val frontend = new Frontend(callback) {
        var underlying: ScalaCompiler#Run = null
        var thread: Thread = null
        var exception: Throwable = null

        override val sources = files

        override def run(): Unit = {
          assert(!isRunning)

          val compiler = new ScalaCompiler(settings, ctx, callback, cache)
          underlying = new compiler.Run

          // Run the compiler in the background in order to make the factory
          // non-blocking, and implement a clean stop action.
          val runnable = new Runnable {
            override def run() = try {
              callback.beginExtractions()
              underlying.compile(sources)
            } finally {
              callback.endExtractions()
              underlying = null
            }
          }

          thread = new Thread(runnable, "stainless compiler")
          thread.setUncaughtExceptionHandler(new Thread.UncaughtExceptionHandler() {
            override def uncaughtException(t: Thread, e: Throwable): Unit = exception = e
          })

          thread.start()
        }

        override def isRunning: Boolean = thread != null && thread.isAlive

        override def onStop(): Unit = {
          if (isRunning) {
            underlying.cancel()
            thread.join()
          }

          rethrow()
        }

        override def onJoin(): Unit = {
          if (isRunning) thread.join()

          rethrow()
        }

        private def rethrow(): Unit = if (exception != null) {
          val e = exception
          exception = null
          ctx.reporter.error(s"Rethrowing exception emitted from within the compiler: ${e.getMessage}")
          throw e
        }
      }

      frontend
    }
  }

  /** Let the frontend analyse the arguments to understand which files should be compiled. */
  private def getFiles(compilerArgs: Seq[String], ctx: inox.Context, settings: NSCSettings): List[String] = {
    val command = new CompilerCommand(compilerArgs.toList, settings) {
      override val cmdName = "stainless"
    }

    if (!command.ok) { ctx.reporter.fatalError("No input program.") }

    command.files
  }

  /** Build settings for the nsc tools. */
  private def buildSettings(ctx: inox.Context): NSCSettings = {
    val settings = new NSCSettings

    // Attempt to find where the scala lib is.
    val scalaLib: String = Option(scala.Predef.getClass.getProtectionDomain.getCodeSource) map {
      _.getLocation.getPath
    } getOrElse { ctx.reporter.fatalError("No Scala library found.") }

    settings.classpath.value = scalaLib
    settings.usejavacp.value = false
    settings.deprecation.value = true
    settings.Yrangepos.value = true
    settings.skip.value = List("patmat")

    settings
  }

}

