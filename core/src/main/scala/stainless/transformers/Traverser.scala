/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package transformers

trait Traverser extends inox.transformers.Traverser {
  val trees: ast.Trees
  import trees._

  override def traverse(e: Expr, env: Env): Unit = e match {
    case MatchExpr(scrut, cases) =>
      traverse(scrut, env)
      cases.foreach { case MatchCase(pat, optGuard, rhs) =>
        traverse(pat, env)
        optGuard.foreach(traverse(_, env))
        traverse(rhs, env)
      }

    case _ => super.traverse(e, env)
  }

  def traverse(pat: Pattern, env: Env): Unit = {
    val (ids, vs, es, tps, pats, _) = deconstructor.deconstruct(pat)
    ids.foreach(traverse(_, env))
    vs.foreach(v => traverse(v.toVal, env))
    es.foreach(traverse(_, env))
    tps.foreach(traverse(_, env))
    pats.foreach(traverse(_, env))
  }
}

trait TreeTraverser extends Traverser with inox.transformers.TreeTraverser {
  import trees._

  def traverse(pat: Pattern): Unit = super.traverse(pat, ())
  override final def traverse(pat: Pattern, env: Env): Unit = traverse(pat)
}
