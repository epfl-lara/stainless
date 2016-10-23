/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package termination

object TerminationComponent extends SimpleComponent {
  val name = "termination"

  val trees: termination.trees.type = termination.trees

  val lowering = inox.ast.SymbolTransformer(new ast.TreeTransformer {
    val s: extraction.trees.type = extraction.trees
    val t: extraction.trees.type = extraction.trees

    override def transform(e: s.Expr): t.Expr = e match {
      case s.Decreases(rank, body) => transform(body)
      case _ => super.transform(e)
    }
  })

  def apply(p: Program { val trees: termination.trees.type }): Unit = {
    val checker = TerminationChecker(p, p.ctx.options)

    
  }
}
