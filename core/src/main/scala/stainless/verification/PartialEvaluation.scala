/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package verification

import scala.concurrent.duration._

trait PartialEvaluation
  extends extraction.CachingPhase
     with extraction.IdentitySorts
     with extraction.SimpleFunctions { self =>

  val s: extraction.Trees
  val t: s.type

  import context._
  import s._

  override protected def getContext(symbols: s.Symbols) = new TransformerContext(symbols)

  protected class TransformerContext(syms: s.Symbols) extends transformers.PartialEvaluatorWithPC {
    override val trees: s.type = s
    override implicit val symbols: syms.type = syms
    override val context = self.context

    override val semantics = extraction.extractionSemantics
  }

  override protected def extractFunction(context: TransformerContext, fd: s.FunDef): t.FunDef = {
    implicit val symbols = context.symbols
    implicit val debugSection = transformers.DebugSectionPartialEval

    val body = exprOps.withoutSpecs(fd.fullBody)
    val expr = body.map(exprOps.withPrecondition(_, exprOps.preconditionOf(fd.fullBody)))

    reporter.debug(s" - Partially evaluating function '${fd.id}' at ${fd.getPos}...")
    reporter.debug(s"   Before: " + expr.getOrElse("no body"))
    val (elapsed, res) = timers.partialeval.runAndGetTime(expr map (e => context.transform(e)))
    reporter.debug(s"   After: " + res.get.getOrElse("no body"))
    reporter.debug(s"   Time elapsed: " + "%.4f".format(elapsed.millis.toUnit(SECONDS)) + " seconds\n")

    val newBody = res.get.map(exprOps.withBody(fd.fullBody, _)).getOrElse(fd.fullBody)

    fd.copy(fullBody = newBody, flags = fd.flags filterNot (_.name == "partialEval"))
  }
}

object PartialEvaluation {
  def apply(trees: extraction.Trees)(implicit ctx: inox.Context): extraction.ExtractionPipeline {
    val s: trees.type
    val t: trees.type
  } = new PartialEvaluation {
    override val s: trees.type = trees
    override val t: trees.type = trees
    override val context = ctx
  }
}
