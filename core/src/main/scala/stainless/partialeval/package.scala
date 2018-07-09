/* Copyright 2009-2018 EPFL, Lausanne */

package stainless

import scala.concurrent.duration._
import scala.language.postfixOps

package object partialeval {

  object DebugSectionPartialEval extends inox.DebugSection("partial-eval")

  object PartialEvaluator {

    private implicit val debugSection = DebugSectionPartialEval

    def apply(p: StainlessProgram, ctx: inox.Context): inox.ast.SymbolTransformer {
      val s: p.trees.type
      val t: p.trees.type
    } = new inox.ast.SymbolTransformer {
      val s: p.trees.type = p.trees
      val t: p.trees.type = p.trees

      import ctx._
      import ctx.{ timers, reporter }

      import p._
      import p.trees._

      val simplifier = p.symbols.simplifier(inox.solvers.PurityOptions.assumeChecked)

      def partialEval(fd: FunDef, p: StainlessProgram): FunDef =  {
        import p._, p.trees._

        val evaluator = new PartialEvaluatorWithPC(p, ctx)

        val (Seq(pre, post), body) = exprOps.deconstructSpecs(fd.fullBody)
        val expr                   = exprOps.reconstructSpecs(Seq(pre), body, fd.fullBody.getType)

        reporter.debug(s" - Partially evaluating function '${fd.id}' at ${fd.getPos}...")
        reporter.debug(s"   Before: " + expr)
        val (elapsed, res) = timers.partialeval.runAndGetTime(evaluator.transform(simplifier.transform(expr)))
        reporter.debug(s"   After: " + res.get)
        reporter.debug(s"   Time elapsed: " + "%.4f".format(elapsed.millis.toUnit(SECONDS)) + " seconds\n")

        val simpl = simplifier.transform(res.get)

        val newBody = exprOps.reconstructSpecs(Seq(pre, post), Some(simpl), fd.fullBody.getType)

        fd.copy(fullBody = newBody, flags = fd.flags.filterNot(_.name == "partialEval"))
      }

      def transform(syms: s.Symbols): t.Symbols = {
        syms.functions.values.toSeq
          .filter(_.flags exists (_.name == "partialEval"))
          .sorted(syms.CallGraphOrderings.functionOrdering.reverse)
          .foldLeft(p) { case (p, fd) => p.withFunctions(Seq(partialEval(fd, p))) }
          .symbols
      }
    }
  }

}
