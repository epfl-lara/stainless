/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package verification

import scala.concurrent.duration._

object DebugSectionPartialEval extends inox.DebugSection("partial-eval")

trait PartialEvaluation
  extends extraction.CachingPhase
     with extraction.IdentitySorts
     with extraction.SimpleFunctions { self =>

  val s: extraction.Trees
  val t: s.type

  import context._
  import s._

  implicit val debugSection = DebugSectionPartialEval

  protected val semantics: inox.SemanticsProvider { val trees: s.type }

  override protected final val funCache = new ExtractionCache[s.FunDef, FunctionResult]((fd, context) => 
    getDependencyKey(fd.id)(context.symbols)
  )

  override protected def getContext(symbols: s.Symbols) = new TransformerContext(symbols)

  protected class TransformerContext(val symbols: s.Symbols) { self0 =>
    import symbols._

    private[this] val simpleSimplifier = new {
      override val trees: s.type = s
      override val symbols: self0.symbols.type = self0.symbols
      override val opts = inox.solvers.PurityOptions.assumeChecked
    } with transformers.PartialEvaluator with inox.transformers.SimplifierWithPath {
      override val pp = Env
    }

    private[this] val solvingSimplifier = new {
      override val trees: s.type = s
      override val symbols: self0.symbols.type = self0.symbols
      override val context = self.context
      override val semantics = self.semantics
      override val opts = inox.solvers.PurityOptions.assumeChecked
    } with transformers.PartialEvaluator with transformers.SimplifierWithSolver {
      override val pp = Env
    }

    private[this] val hasPartialEvalFlag: Set[Identifier] =
      symbols.functions.values.filter(_.flags contains s.PartialEval).map(_.id).toSet

    private[this] val isSynthetic: Set[Identifier] =
      symbols.functions.values.filter(_.flags contains s.Synthetic).map(_.id).toSet

    private[this] def invocationsToEval(id: Identifier): Set[Identifier] =
      symbols.callees(id) & hasPartialEvalFlag

    def shouldPartialEval(fd: FunDef): Boolean =
      invocationsToEval(fd.id).nonEmpty && !(fd.flags contains Synthetic)

    private[this] def partialEval(fi: FunctionInvocation, path: Path, simple: Boolean = false): Expr = {
      if (simple)
        simpleSimplifier.transform(fi, simpleSimplifier.Env(path))
      else
        solvingSimplifier.transform(fi, solvingSimplifier.Env(path))
    }

    final def transform(fd: FunDef): FunDef = {
      val toEval = invocationsToEval(fd.id)

      def eval(e: Expr): Expr = symbols.transformWithPC(e)((e, path, op) => e match {
        case fi: FunctionInvocation if fi.id != fd.id && toEval(fi.id) =>
          reporter.debug(s" - Partially evaluating call to '${toEval.mkString(", ")}' in '${fd.id}' at ${fd.getPos}...")
          reporter.debug(s"   Path condition: $path")
          reporter.debug(s"   Before: $fi")

          val (elapsed, res) = timers.partialeval.runAndGetTime {
            partialEval(fi, path, simple = isSynthetic(fi.id))
          }

          reporter.debug(s"   After: ${res.get}")
          reporter.debug(s"   Time elapsed: " + "%.4f".format(elapsed.millis.toUnit(SECONDS)) + " seconds\n")
          res.get

        case _ => op.sup(e, path)
      })

      fd.copy(fullBody = eval(fd.fullBody), flags = fd.flags filterNot (_ == PartialEval))
    }
  }

  override protected def extractFunction(context: TransformerContext, fd: FunDef): FunDef = {
    if (context shouldPartialEval fd) context.transform(fd) else fd
  }
}

object PartialEvaluation {
  def apply(tr: extraction.Trees)(
    implicit ctx: inox.Context, sems: inox.SemanticsProvider { val trees: tr.type }
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
