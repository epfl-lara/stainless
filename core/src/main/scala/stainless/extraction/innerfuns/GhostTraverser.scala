/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package extraction
package innerfuns

trait GhostTraverser extends transformers.GhostTraverser {
  val trees: Trees
  import trees._

  private[this] var innerFuns = Map.empty[Identifier, LocalFunDef]

  private[this] def withInnerFuns[A](fds: Seq[LocalFunDef])(a: => A): A = {
    val prev = innerFuns
    innerFuns = fds.map(fd => fd.id -> fd).toMap
    val res = a
    innerFuns = prev
    res
  }

  override def traverse(e: Expr, ctx: GhostContext): Unit = e match {
    case LetRec(defs, body) =>
      withInnerFuns(defs) {
        defs.foreach(traverse(_, ctx))
        traverse(body, ctx)
      }

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
    val innerCtx = ctx.inGhost(fd.flags contains Ghost)
    traverse(fd.id, innerCtx)
    fd.tparams map (traverse(_, innerCtx))
    fd.params map (traverse(_, innerCtx))
    traverse(fd.returnType, innerCtx)
    traverse(fd.fullBody, innerCtx)
    fd.flags map (traverse(_, innerCtx))
  }
}



