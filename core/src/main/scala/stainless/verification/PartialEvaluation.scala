/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification

import scala.concurrent.duration._

object DebugSectionPartialEval extends inox.DebugSection("partial-eval")

class PartialEvaluation(override val s: extraction.Trees)
                       (override val t: s.type,
                        protected val semantics: inox.SemanticsProvider { val trees: s.type })
                       (using override val context: inox.Context)
  extends extraction.CachingPhase
     with extraction.IdentitySorts
     with extraction.SimpleFunctions { self =>

  import context.{given, _}
  import s._

  given givenDebugSection: DebugSectionPartialEval.type = DebugSectionPartialEval

  override protected final val funCache = new ExtractionCache[s.FunDef, FunctionResult]((fd, context) => 
    getDependencyKey(fd.id)(using context.symbols)
  )

  override protected def getContext(symbols: s.Symbols) = new TransformerContext(symbols)

  protected class TransformerContext(val symbols: s.Symbols) { self0 =>
    import symbols.{given, _}

    private[this] class SimpleSimplifier(override val trees: self.s.type,
                                         override val symbols: self0.symbols.type,
                                         override val s: self.s.type,
                                         override val t: self.s.type)
                                        (using override val opts: inox.solvers.PurityOptions)
      extends transformers.PartialEvaluator with inox.transformers.SimplifierWithPath {
      override val pp = Env
    }
    private[this] val simpleSimplifier =
      new SimpleSimplifier(s, self0.symbols, s, s)(using inox.solvers.PurityOptions.assumeChecked)

    private[this] class SolvingSimplifier(override val trees: self.s.type,
                                          override val symbols: self0.symbols.type,
                                          override val s: self.s.type,
                                          override val t: self.s.type,
                                          override val context: inox.Context,
                                          override val semantics: self.semantics.type)
                                         (using override val opts: inox.solvers.PurityOptions)
      extends transformers.PartialEvaluator with transformers.SimplifierWithSolver {
      override val pp = Env
    }
    private[this] val solvingSimplifier =
      new SolvingSimplifier(s, self0.symbols, s, s, self.context, self.semantics)(using inox.solvers.PurityOptions.assumeChecked)

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
    using ctx: inox.Context, sems: inox.SemanticsProvider { val trees: tr.type }
  ): extraction.ExtractionPipeline {
    val s: tr.type
    val t: tr.type
  } = {
    class Impl(override val s: tr.type, override val t: tr.type, override val semantics: sems.type)
      extends PartialEvaluation(s)(t, semantics)
    new Impl(tr, tr, sems)
  }
}
