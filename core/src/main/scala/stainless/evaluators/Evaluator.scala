/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package evaluators

import inox.evaluators.DeterministicEvaluator

object optCodeGen extends inox.FlagOptionDef("codegen", false)

object Evaluator {
  def apply(p: StainlessProgram, ctx: inox.Context):
            DeterministicEvaluator { val program: p.type } = {
    if (ctx.options.findOptionOrDefault(optCodeGen)) CodeGenEvaluator(p, ctx)
    else RecursiveEvaluator(p, ctx)
  }
}
