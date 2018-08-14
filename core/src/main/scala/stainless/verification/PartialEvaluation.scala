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

  protected abstract class FastTransformer extends {
    override val trees: s.type = s
    override val context = self.context
    override val semantics = self.semantics
    override implicit val opts: inox.solvers.PurityOptions = inox.solvers.PurityOptions.assumeChecked
  } with transformers.FastPartialEvaluator 

  protected abstract class SlowTransformer extends {
    override val trees: s.type = s
    override val context = self.context
    override val semantics = self.semantics
    override implicit val opts: inox.solvers.PurityOptions = inox.solvers.PurityOptions.assumeChecked
  } with transformers.SlowPartialEvaluator

  protected class TransformerContext(val symbols: s.Symbols) { self =>
    import symbols.Path

    private[this] val fastTransformer = new {
      override implicit val symbols: self.symbols.type = self.symbols
    } with FastTransformer

    private[this] val slowTransformer = new {
      override implicit val symbols: self.symbols.type = self.symbols
    } with SlowTransformer

    private[this] val hasPartialEvalFlag: Set[Identifier] =
      symbols.functions.values.filter(_.flags contains s.PartialEval).map(_.id).toSet

    private[this] val isSynthetic: Set[Identifier] =
      symbols.functions.values.filter(_.flags contains s.Synthetic).map(_.id).toSet

    private[this] def invocationsToEval(id: Identifier): Set[Identifier] =
      symbols.callees(id) & hasPartialEvalFlag

    def shouldPartialEval(fd: s.FunDef): Boolean =
      invocationsToEval(fd.id).nonEmpty

    private[this] def partialEval(fi: s.FunctionInvocation, path: Path, fast: Boolean = false): s.Expr = {
      if (fast)
        fastTransformer.transform(fi, fastTransformer.CNFPath(path))
      else
        slowTransformer.transform(fi, slowTransformer.SlowPath(path))
    }

    final def transform(fd: s.FunDef): t.FunDef = {
      implicit val debugSection = transformers.DebugSectionPartialEval

      val toEval = invocationsToEval(fd.id)

      def eval(e: s.Expr): s.Expr = symbols.transformWithPC(e)((e, path, op) => e match {
        case fi: s.FunctionInvocation if fi.id != fd.id && toEval(fi.id) =>
          reporter.debug(s" - Partially evaluating call to '${toEval.mkString(", ")}' in '${fd.id}' at ${fd.getPos}...")
          reporter.debug(s"   Path condition: $path")
          reporter.debug(s"   Before: $fi")

          val (elapsed, res) = timers.partialeval.runAndGetTime {
            partialEval(fi, path, fast = isSynthetic(fi.id))
          }

          reporter.debug(s"   After: ${res.get}")
          reporter.debug(s"   Time elapsed: " + "%.4f".format(elapsed.millis.toUnit(SECONDS)) + " seconds\n")
          res.get

        case _ => op.superRec(e, path)
      })

      fd.copy(fullBody = eval(fd.fullBody), flags = fd.flags filterNot (_ == s.PartialEval))
    }
  }

  override protected def extractFunction(context: TransformerContext, fd: s.FunDef): t.FunDef = {
    if (context shouldPartialEval fd) context.transform(fd) else fd
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
