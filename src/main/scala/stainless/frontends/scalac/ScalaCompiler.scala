/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package frontends.scalac

import scala.tools.nsc.{Global,Settings=>NSCSettings}
import scala.reflect.internal.Positions

class ScalaCompiler(settings : NSCSettings, ctx: LeonContext) extends Global(settings, new SimpleReporter(settings, ctx.reporter)) with Positions {

  object leonExtraction extends {
    val global: ScalaCompiler.this.type = ScalaCompiler.this
    val runsAfter = List[String]("refchecks")
    val runsRightAfter = None
    val ctx = ScalaCompiler.this.ctx
  } with LeonExtraction

  object saveImports extends {
    val global: ScalaCompiler.this.type = ScalaCompiler.this
    val runsAfter = List[String]("pickler")
    val runsRightAfter = None
    val ctx = ScalaCompiler.this.ctx
  } with SaveImports
  
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
      saveImports             -> "save imports to pass to leonExtraction",
      refChecks               -> "reference/override checking, translate nested objects",
      leonExtraction          -> "extracts leon trees out of scala trees"
    )
    phs foreach { phasesSet += _._1 }
  }

  class Run extends super.Run {
    override def progress(current: Int, total: Int) {
      ctx.reporter.onCompilerProgress(current, total)
    }
  }
}
