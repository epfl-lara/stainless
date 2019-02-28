/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package verification

import scala.concurrent.duration._

import stainless.utils.StringUtils.indent

object DebugSectionTermRewrite extends inox.DebugSection("term-rewrite")

trait TermRewriting
  extends extraction.CachingPhase
     with extraction.IdentitySorts
     with extraction.SimpleFunctions { self =>

  val s: extraction.Trees
  val t: s.type

  import context._
  import s._

  implicit val debugSection = DebugSectionTermRewrite

  protected val semantics: inox.SemanticsProvider { val trees: s.type }

  override protected final val funCache = new ExtractionCache[s.FunDef, FunctionResult]((fd, context) => 
    getDependencyKey(fd.id)(context.symbols)
  )

  override protected def getContext(symbols: s.Symbols) = new TransformerContext(symbols)

  protected class TransformerContext(val symbols: s.Symbols) { self0 =>
    import symbols._

    private[this] lazy val termRewriter = new {
      override val trees: s.type = s
      override val symbols: self0.symbols.type = self0.symbols
      override val context = self.context
      override val semantics = self.semantics
      override val opts = inox.solvers.PurityOptions.assumeChecked
      override val rulesFuns = self0.rulesFuns
    } with transformers.TermRewriter with transformers.SimplifierWithSolver {
      override val pp = Env
    }

    private[this] val rulesFuns: List[FunDef] =
      symbols.functions.values
        .filter(_.flags contains s.RewriteRule)
        .toList

    final def transform(fd: FunDef): FunDef = {
      reporter.debug(s"Rewriting function '${fd.id.asString}'...")
      reporter.debug(s" - Rewrite rules: ${rulesFuns.map(_.id.asString).mkString(", ")}")
      reporter.debug(s" - Before: ${indent(fd.fullBody.asString, 11, firstLine = false)}")
      val (rewritten, rulesApplied) = termRewriter.rewrite(fd.fullBody)
      reporter.debug(s" - After:  ${indent(rewritten.asString, 11, firstLine = false)}")
      reporter.debug(s" - Rules applied: ${rulesApplied.map(_.asString).toList.mkString(", ")}")
      fd.copy(fullBody = rewritten)
    }
  }

  override protected def extractFunction(context: TransformerContext, fd: FunDef): FunDef = {
    if (fd.flags contains s.Rewrite) context.transform(fd)
    else fd
  }
}

object TermRewriting {
  def apply(tr: extraction.Trees)(
    implicit ctx: inox.Context, sems: inox.SemanticsProvider { val trees: tr.type }
  ): extraction.ExtractionPipeline {
    val s: tr.type
    val t: tr.type
  } = new TermRewriting {
    override val s: tr.type = tr
    override val t: tr.type = tr
    override val context = ctx
    override val semantics = sems
  }
}
