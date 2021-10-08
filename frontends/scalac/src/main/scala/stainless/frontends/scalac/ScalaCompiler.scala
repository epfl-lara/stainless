/* Copyright 2009-2021 EPFL, Lausanne */

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

  private def kind(sym: Global#Symbol): String = {
    if (sym.isPackageClass) "0"
    else if (sym.isModule) "1"
    else if (sym.isModuleClass) "2"
    else if (sym.isClass) "c" + sym.id
    else if (sym.isMethod) "m" + sym.id
    else if (sym.isType) "tp" + sym.id
    else if (sym.isTerm) "t" + sym.id // Many things are terms... Fallback to its id
    else ???
  }
}

class SymbolMapping {
  import SymbolMapping.getPath

  private[this] val ignoredClasses = Set(
    "scala.Any",
    "scala.AnyRef",
    "scala.Product",
    "scala.Serializable",
    "java.lang.Object",
    "java.lang.Serializable",
  )

  // Note: We can't compare with the global symbols here because
  // the symbol mapping class is re-used across compiler runs
  // and thus across `Global` instances, so we have to check
  // against the full symbol name instead. - @romac
  def isIgnored(sym: Global#Symbol): Boolean = {
    val name = sym.fullNameAsName('.').decode.trim
    ignoredClasses contains name
  }

  def topmostAncestor(sym: Global#Symbol): Global#Symbol = {
    sym.overrideChain
      .filterNot(s => isIgnored(s.owner))
      .lastOption
      .getOrElse(sym)
  }

  /** Get the identifier associated with the given [[sym]], creating a new one if needed. */
  def fetch(sym: Global#Symbol): SymbolIdentifier = {
    val path = getPath(sym)
    s2i.getOrElseUpdate(path, {
      val top = topmostAncestor(sym)
      val symbol = s2s.getOrElseUpdate(top, {
        val name = sym.fullNameAsName('.').decode.trim
        ast.Symbol(if (name endsWith "$") name.init else name)
      })

      SymbolIdentifier(symbol)
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

class ScalaCompiler(settings: NSCSettings, val ctx: inox.Context, val callback: CallBack, val cache: SymbolMapping)
  extends Global(settings, new SimpleReporter(settings, ctx.reporter))
     with Positions { self =>

  // Normally, we would initialize the fields with early-initializer. Since this feature has been dropped in Scala 3,
  // we work-around that by definining a dummy class overriding all members.
  // This ensure that these fields are correctly initialized
  class StainlessExtractionImpl(override val global: self.type,
                                override val phaseName: String,
                                override val runsAfter: List[String],
                                override val runsRightAfter: Option[String],
                                override val runsBefore: List[String],
                                override val ctx: self.ctx.type,
                                override val callback: self.callback.type,
                                override val cache: self.cache.type)
    extends StainlessExtraction with ASTExtractors(global)

  val stainlessExtraction = new StainlessExtractionImpl(
    global = self,
    phaseName = "stainless",
    runsAfter = List("typer"),
    runsRightAfter = None,
    runsBefore = List("patmat"),
    ctx = self.ctx,
    callback = self.callback,
    cache = self.cache
  )

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

        val args = allCompilerArguments(ctx, compilerArgs)
        val settings = buildSettings(ctx)

        override val sources: List[String] = getFiles(args, ctx, settings)

        override def initRun(): Unit = {
          assert(underlying == null)
          val compiler = new ScalaCompiler(settings, ctx, this.callback, cache)
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
    settings.usejavacp.value = false
    settings.feature.value = true
    settings.unchecked.value = true
    settings.deprecation.value = true
    settings.Yrangepos.value = true
    // FIXME: When compiling the Stainless lib sources, Scalac looks (for some reasons) for stainless/package.class.
    //  This compiled packaged.class belongs to stainless-core and has nothing to do with Stainless library;
    //  it is furthermore compiled with Scala 3.
    //  Scalac complains that it can't ready TASTy files unless the following option is set.
    //  The ideal solution would be to somehow inform Scalac to not look for stainless-core .class file.
    //  Note that adding a dummy stainless/package.scala to Stainless lib does not resolve the issue.
    settings.YtastyReader.value = true

    settings
  }

}

