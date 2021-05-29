/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package evaluators

import inox.evaluators.DeterministicEvaluator

object optCodeGen extends inox.FlagOptionDef("codegen", false)

object Evaluator {
  val RecursiveEvaluatorName: String = "default recursive evaluator"
  val CodeGenEvaluatorName: String = "codegen evaluator"
  var kind: String = RecursiveEvaluatorName
  def apply(p: StainlessProgram, ctx: inox.Context):
        DeterministicEvaluator { val program: p.type } =
  {
     if (ctx.options.findOptionOrDefault(optCodeGen)) {
      kind = CodeGenEvaluatorName
      CodeGenEvaluator(p, ctx)
    } else RecursiveEvaluator(p, ctx)
  }
}
