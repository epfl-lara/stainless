/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package evaluators

class FunctionSplitting private(override val sourceProgram: Program,
                                override val targetProgram: inox.Program { val trees: sourceProgram.trees.type })
  extends inox.transformers.ProgramTransformer {

  protected object encoder extends sourceProgram.trees.ConcreteIdentityTreeTransformer
  protected object decoder extends sourceProgram.trees.ConcreteIdentityTreeTransformer
}

object FunctionSplitting {
  private def computeTargetProgram(sourceProgram: Program, maxSize: Int, maxSlots: Int): inox.Program { val trees: sourceProgram.trees.type } =
    new inox.Program {
      val trees: sourceProgram.trees.type = sourceProgram.trees
      import trees._

      val symbols = NoSymbols
        .withSorts(sourceProgram.symbols.sorts.values.toSeq)
        .withFunctions(sourceProgram.symbols.functions.values.toSeq.map { fd =>
          def rec(e: Expr): (Expr, Int, Int) = e match {
            // TODO: consider splitting expressions within lambdas/foralls as well.
            //       This is feasible by making sure the normalized structures remain the
            //       same even after splitting.
            case (_: Choose) | (_: Forall) | (_: Lambda) => (e, 0, 0)

            case Operator(es, recons) =>
              val (nes, sizes, slotss) = es.map(rec).unzip3
              val size = sizes.sum + 1
              val slots = slotss.sum + (if (e.isInstanceOf[Let]) 1 else 0)
              if (size > maxSize || slots > maxSlots) {
                // Lambdas are compiled into new classes/functions so placing the
                // code underneath a lambda will make sure both the slot and size
                // requirements of the resulting classfiles are met.
                (Application(Lambda(Seq(), recons(nes)), Seq()), 0, 0)
              } else {
                (recons(nes), size, slots)
              }
          }

          fd.copy(fullBody = rec(fd.fullBody)._1)
        })
    }

  def apply(p: Program, size: Int = 500, slots: Int = 100): FunctionSplitting { val sourceProgram: p.type } = {
    class Impl(override val sourceProgram: p.type) extends FunctionSplitting(sourceProgram, computeTargetProgram(p, size, slots))
    new Impl(p)
  }
}
