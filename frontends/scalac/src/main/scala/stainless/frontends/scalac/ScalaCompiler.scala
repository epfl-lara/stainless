/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package frontends.scalac

import ast.SymbolIdentifier
import frontend.{ Frontend, ThreadedFrontend, FrontendFactory, CallBack }

import scala.tools.nsc.{ Global, Settings => NSCSettings, CompilerCommand }
import scala.reflect.internal.Positions

import scala.collection.mutable.{ Map => MutableMap }

object SymbolMapping {
  def getPath(sym: Global#Symbol): String =
    sym.ownerChain.reverse map { s => s"${s.name}#${kind(s)}" } mkString "."

  def empty = new SymbolMapping()

  /**
   * To avoid suffering too much from changes in symbols' id, we generate a
   * more stable kind to disambiguate symbols. This allows --watch to not be
   * fooled by the insertion/deletion of symbols (e.g. new top level classes)
   * but unfortunately not methods because overloading/generics makes things
   * ambiguous and hard to unify.
   */
  private def kind(sym: Global#Symbol): String = {
    if (sym.isPackageClass) "0"
    else if (sym.isModule) "1"
    else if (sym.isModuleClass) "2"
    else if (sym.isClass) "3"
    else if (sym.isMethod) "m" + sym.id
    else if (sym.isType) "5"
    else if (sym.isTerm) "t" + sym.id // Many things are terms... Fallback to its id
    else ???
  }
}

class SymbolMapping {
  import SymbolMapping.getPath

  /** Get the identifier associated with the given [[sym]], creating a new one if needed. */
  def fetch(sym: Global#Symbol): SymbolIdentifier = {
    val path = getPath(sym)
    s2i.getOrElse(path, {
      val top = if (sym.overrideChain.nonEmpty) sym.overrideChain.last else sym
      val symbol = s2s.getOrElse(top, {
        val name = sym.fullNameAsName('.').decode.trim
        val res = ast.Symbol(if (name endsWith "$") name.init else name)
        s2s(top) = res
        res
      })

      val res = SymbolIdentifier(symbol)
      s2i(path) = res
      res
    })
  }

  /** Get the identifier for the class invariant of [[sym]]. */
  def fetchInvIdForClass(sym: Global#Symbol): SymbolIdentifier = {
    val id = fetch(sym)
    invs.getOrElse(id, {
      val res = SymbolIdentifier(invSymbol)
      invs(id) = res
      res
    })
  }

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
    val runsAfter = List[String]("typer")
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
    override val libraryPaths: Seq[String]
  ) extends FrontendFactory {

    override def apply(ctx: inox.Context, compilerArgs: Seq[String], callback: CallBack): Frontend =
      new ThreadedFrontend(callback, ctx) {
        var underlying: ScalaCompiler#Run = _
        val cache = SymbolMapping.empty

        val args = allCompilerArguments(compilerArgs)
        val settings = buildSettings(ctx)

        override val sources = getFiles(args, ctx, settings)

        override def initRun(): Unit = {
          assert(underlying == null)
          val compiler = new ScalaCompiler(settings, ctx, callback, cache)
          underlying = new compiler.Run
        }

        override def onRun(): Unit = {
          underlying.compile(sources)
        }

        override def onEnd(): Unit = {
          underlying = null
        }

        override def onStop(thread: Thread): Unit = {
          underlying.cancel()
          thread.join()
        }
      }
  }

  /** Let the frontend analyses the arguments to understand which files should be compiled. */
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
    settings.usejavacp.value = stainless.BuildInfo.useJavaClassPath
    settings.deprecation.value = true
    settings.Yrangepos.value = true

    settings
  }

}

