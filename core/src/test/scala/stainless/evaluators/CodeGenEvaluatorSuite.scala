/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package evaluators

import inox.evaluators._

class CodeGenEvaluatorSuite extends EvaluatorSuite {

  override def evaluator(ctx: inox.Context): DeterministicEvaluator { val program: inox.InoxProgram } = {
    object lifter extends inox.ast.ProgramEncoder {
      val sourceProgram: program.type = program
      val t: stainless.trees.type = stainless.trees

      object encoder extends inox.ast.TreeTransformer {
        val s: inox.trees.type = inox.trees
        val t: stainless.trees.type = stainless.trees
      }

      object decoder extends inox.ast.TreeTransformer {
        val s: stainless.trees.type = stainless.trees
        val t: inox.trees.type = inox.trees
      }
    }

    EncodingEvaluator(program)(lifter)(CodeGenEvaluator(lifter.targetProgram, ctx))
  }
}

