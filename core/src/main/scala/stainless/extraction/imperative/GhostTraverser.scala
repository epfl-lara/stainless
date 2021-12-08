/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package imperative

trait GhostTraverser extends oo.GhostTraverser {
  val trees: Trees
  import trees._

  override def traverse(e: Expr, ctx: GhostContext): Unit = e match {
    case Snapshot(body) =>
      traverse(body, ctx.withinGhost)

    case _ => super.traverse(e, ctx)
  }

}
