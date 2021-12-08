/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package methods

trait GhostTraverser extends imperative.GhostTraverser {
  val trees: Trees
  import trees._

  override def traverse(e: Expr, ctx: GhostContext): Unit = e match {
    case MethodInvocation(rec, id, _, args) if symbols.getFunction(id).flags contains Ghost =>
      super.traverse(e, ctx.withinGhost)

    case MethodInvocation(rec, id, tps, args) =>
      val fd = symbols.getFunction(id)

      traverse(rec, ctx)
      tps.foreach(traverse(_, ctx))

      (fd.params zip args) foreach { case (vd, arg) =>
        traverse(arg, ctx.inGhost(vd.flags contains Ghost))
      }

    case _ => super.traverse(e, ctx)
  }
}
