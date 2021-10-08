/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package innerfuns

trait GhostTraverser extends transformers.GhostTraverser {
  val trees: Trees
  import trees._

  private[this] var localFuns = Map.empty[Identifier, LocalFunDef]

  private[this] def withLocalFuns[A](fds: Seq[LocalFunDef])(a: => A): A = {
    val prev = localFuns
    localFuns ++= fds.map(fd => fd.id -> fd)
    val res = a
    localFuns = prev
    res
  }

  override def traverse(fd: FunDef): Unit = {
    val lfds = exprOps.collect[LocalFunDef] {
      case LetRec(lfds, _) => lfds.toSet
      case _ => Set.empty
    } (fd.fullBody)

    withLocalFuns(lfds.toSeq) {
      super.traverse(fd)
    }
  }

  override def traverse(e: Expr, ctx: GhostContext): Unit = e match {
    case LetRec(defs, body) =>
      withLocalFuns(defs) {
        defs.foreach(traverse(_, ctx))
        traverse(body, ctx)
      }

    case alr: ApplyLetRec if localFuns(alr.id).flags contains Ghost =>
      super.traverse(alr, ctx.withinGhost)

    case ApplyLetRec(id, tparams, tpe, tps, args) =>
      val fd = localFuns(id)
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
    val localCtx = ctx.inGhost(fd.flags contains Ghost)
    traverse(fd.id, localCtx)
    fd.tparams map (traverse(_, localCtx))
    fd.params map (traverse(_, localCtx))
    traverse(fd.returnType, localCtx)
    traverse(fd.fullBody, localCtx)
    fd.flags map (traverse(_, localCtx))
  }
}
