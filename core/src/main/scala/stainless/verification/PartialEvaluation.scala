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

  protected val semantics: inox.SemanticsProvider { val trees: s.type }

  override protected def getContext(symbols: s.Symbols) = new TransformerContext(symbols)

  protected class TransformerContext(syms: s.Symbols) extends transformers.PartialEvaluatorWithPC {
    override val trees: s.type = s
    override implicit val symbols: syms.type = syms
    override val context = self.context
    override val semantics = self.semantics

    val toPartialEval: Set[Identifier] =
      syms.functions.values.filter(_.flags contains s.PartialEval).map(_.id).toSet

    def toEval(id: Identifier): Set[Identifier] =
      syms.callees(id) & toPartialEval
  }

  override protected def extractFunction(context: TransformerContext, fd: s.FunDef): t.FunDef = {
    val toEval = context.toEval(fd.id)
    val res = if (toEval.nonEmpty) partialEval(context, fd, toEval) else fd

    res.copy(flags = fd.flags filterNot (_ == s.PartialEval))
  }

  protected def partialEval(context: TransformerContext, fd: s.FunDef, toEval: Set[Identifier]): t.FunDef = {
    implicit val symbols = context.symbols
    implicit val debugSection = transformers.DebugSectionPartialEval

    def eval(e: s.Expr): s.Expr = symbols.transformWithPC(e)((e, path, op) => e match {
      case fi: s.FunctionInvocation if fi.id != fd.id && toEval.contains(fi.id) =>
        reporter.debug(s" - Partially evaluating call to '${toEval.mkString(", ")}' in '${fd.id}' at ${fd.getPos}...")
        reporter.debug(s"   Path condition: $path")
        reporter.debug(s"   Before: $fi")
        val (elapsed, res) = timers.partialeval.runAndGetTime(context.transform(fi, path))
        reporter.debug(s"   After: ${res.get}")
        reporter.debug(s"   Time elapsed: " + "%.4f".format(elapsed.millis.toUnit(SECONDS)) + " seconds\n")
        res.get

      case _ => op.superRec(e, path)
    })

    fd.copy(fullBody = eval(fd.fullBody))
  }

}

object PartialEvaluation {
  def apply(tr: extraction.Trees)(
    implicit ctx: inox.Context,
    sems: inox.SemanticsProvider { val trees: tr.type }
  ): extraction.ExtractionPipeline {
    val s: tr.type
    val t: tr.type
  } = new PartialEvaluation {
    override val s: tr.type = tr
    override val t: tr.type = tr
    override val context = ctx
    override val semantics = sems
  }
}
