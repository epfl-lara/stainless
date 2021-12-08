/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package transformers

trait GhostTraverser extends DefinitionTraverser { self =>
  val trees: ast.Trees
  import trees._
  val symbols: Symbols
  import symbols.{given, _}

  lazy val deconstructor: inox.ast.TreeDeconstructor {
    val s: self.trees.type
    val t: self.trees.type
  } = self.trees.getDeconstructor(self.trees)

  class GhostContext(val isGhost: Boolean) { self =>
    @inline def inGhost(isGhost: Boolean): GhostContext =
      new GhostContext(self.isGhost || isGhost)

    @inline def withinGhost: GhostContext =
      new GhostContext(true)
  }

  override type Env = GhostContext
  override val initEnv: GhostContext = new GhostContext(false)

  override def traverse(fd: FunDef): Unit = {
    val initCtx = initEnv.inGhost(fd.flags contains Ghost)
    traverse(fd.id, initCtx)
    fd.tparams.foreach(traverse(_, initCtx))
    fd.params.foreach(traverse(_, initCtx))
    traverse(fd.returnType, initCtx)
    traverse(fd.fullBody, initCtx)
    fd.flags.foreach(traverse(_, initCtx))
  }

  override def traverse(vd: ValDef, ctx: GhostContext): Unit = {
    super.traverse(vd, ctx.inGhost(vd.flags contains Ghost))
  }

  override def traverse(e: Expr, ctx: GhostContext): Unit = e match {
    case v: Variable =>
      super.traverse(v, ctx.inGhost(v.flags contains Ghost))

    case Annotated(body, flags) =>
      super.traverse(e, ctx.inGhost(flags contains Ghost))

    case Decreases(measure, body) =>
      traverse(measure, ctx.withinGhost)
      traverse(body, ctx)

    case FunctionInvocation(id, _, _) if symbols.getFunction(id).flags contains Ghost =>
      super.traverse(e, ctx.withinGhost)

    case FunctionInvocation(id, tps, args) =>
      val fd = symbols.getFunction(id)

      tps.foreach(traverse(_, ctx))

      (fd.params zip args) foreach { case (vd, arg) =>
        traverse(arg, ctx.inGhost(vd.flags contains Ghost))
      }

    case ADT(id, tps, args) =>
      tps.foreach(traverse(_, ctx))
      (symbols.getConstructor(id).fields zip args) foreach { case (vd, arg) =>
        traverse(arg, ctx.inGhost(vd.flags contains Ghost))
      }

    case _ => super.traverse(e, ctx)
  }

}