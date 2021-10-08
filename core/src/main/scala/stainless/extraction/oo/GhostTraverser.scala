/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package oo

trait GhostTraverser extends innerfuns.GhostTraverser {
  val trees: Trees
  import trees._
  import symbols.given

  override def traverse(e: Expr, ctx: GhostContext): Unit = e match {
    case ClassConstructor(ct, args) =>
      traverse(ct, ctx)

      (ct.tcd.fields zip args).foreach { case (vd, arg) =>
        traverse(arg, ctx.inGhost(vd.flags contains Ghost))
      }

    case _ => super.traverse(e, ctx)
  }
}
