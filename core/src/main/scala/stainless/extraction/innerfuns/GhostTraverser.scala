/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package extraction
package innerfuns

import scala.collection.mutable.{Map => MutableMap}

trait GhostTraverser extends transformers.GhostTraverser {
  val trees: Trees
  import trees._

  private[this] val innerFuns = MutableMap.empty[Identifier, LocalFunDef]

  override def traverse(e: Expr, ctx: GhostContext): Unit = e match {
    case LetRec(defs, body) =>
      defs.foreach(traverse(_, ctx))
      traverse(body, ctx)

    case alr: ApplyLetRec if innerFuns(alr.id).flags contains Ghost =>
      super.traverse(alr, ctx.withinGhost)

    case ApplyLetRec(id, tparams, tpe, tps, args) =>
      val fd = innerFuns(id)
      traverse(id, ctx)
      tparams.foreach(traverse(_, ctx))
      traverse(tpe, ctx)
      tps.foreach(traverse(_, ctx))
      fd.params.zip(args) foreach { case (vd, arg) =>
        traverse(arg, ctx.inGhost(vd.flags contains Ghost))
      }

    case _ => super.traverse(e, ctx)
  }

  def traverse(fd: LocalFunDef, ctx: GhostContext): Unit = {
    innerFuns += (fd.id -> fd)

    val innerCtx = ctx.inGhost(fd.flags contains Ghost)
    traverse(fd.id, innerCtx)
    fd.tparams map (traverse(_, innerCtx))
    fd.params map (traverse(_, innerCtx))
    traverse(fd.returnType, innerCtx)
    traverse(fd.fullBody, innerCtx)
    fd.flags map (traverse(_, innerCtx))
  }
}



