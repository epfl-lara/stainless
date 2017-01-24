/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package evaluators

import inox.evaluators.DeterministicEvaluator

object optCodeGen extends inox.FlagOptionDef("codegen", false)

object Evaluator {
  def apply(p: StainlessProgram, opts: inox.Options):
            DeterministicEvaluator { val program: p.type } = {
    if (opts.findOptionOrDefault(optCodeGen)) CodeGenEvaluator(p, opts)
    else RecursiveEvaluator(p, opts)
  }
}
