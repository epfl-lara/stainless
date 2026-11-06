/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package evaluators

import inox.evaluators._

class CodeGenEvaluatorSuite extends EvaluatorSuite {

  override def evaluator(ctx: inox.Context): DeterministicEvaluator { val program: inox.InoxProgram } = {
    class Encoder(override val s: inox.trees.type, override val t: stainless.trees.type)
      extends inox.transformers.ConcreteTreeTransformer(s, t)

    class Decoder(override val s: stainless.trees.type, override val t: inox.trees.type)
      extends inox.transformers.ConcreteTreeTransformer(s, t)

    class Lifter(override val sourceProgram: program.type,
                 override val t: stainless.trees.type,
                 override val encoder: Encoder,
                 override val decoder: Decoder)
      extends inox.transformers.ProgramEncoder(t, sourceProgram, encoder, decoder)()

    val lifter = new Lifter(program, stainless.trees, new Encoder(inox.trees, stainless.trees), new Decoder(stainless.trees, inox.trees))
    EncodingEvaluator(program)(lifter)(CodeGenEvaluator(lifter.targetProgram, ctx))
  }

  test("Expression too large for a JVM method") {
    import inox.trees._

    val e = evaluator(ctx)
    val x = ValDef.fresh("x", IntegerType())

    def sum(from: Int, to: Int): Expr = {
      if (from == to) Times(x.toVariable, IntegerLiteral(from))
      else {
        val mid = (from + to) / 2
        Plus(sum(from, mid), sum(mid + 1, to))
      }
    }

    // The expression is compiled to a single method, whose code exceeds the 64 KB that the JVM
    // accepts. The JVM then rejects the class with a `ClassFormatError`, which must be reported
    // as a failed evaluation and not thrown.
    eval(e, sum(1, 9000), Map(x -> IntegerLiteral(7))).failed
  }
}

