/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package extraction
package innerclasses

import scala.collection.mutable.{Map => MutableMap}

trait GhostTraverser extends methods.GhostTraverser with DefinitionTraverser {
  val trees: Trees
  import trees._

  private[this] var innerClasses = Map.empty[Identifier, LocalClassDef]

  private[this] def withInnerClasses[A](fds: Seq[LocalClassDef])(a: => A): A = {
    val prev = innerClasses
    innerClasses = fds.map(fd => fd.id -> fd).toMap
    val res = a
    innerClasses = prev
    res
  }

  override def traverse(lcd: LocalClassDef, ctx: GhostContext): Unit = {
    super.traverse(lcd, ctx.inGhost(lcd.flags contains Ghost))
  }

  override def traverse(lmd: LocalMethodDef, ctx: GhostContext): Unit = {
    super.traverse(lmd, ctx.inGhost(lmd.flags contains Ghost))
  }

  override def traverse(e: Expr, ctx: GhostContext): Unit = e match {
    case LocalThis(lct) =>
      traverse(lct, ctx)

    case LetClass(lcds, body) =>
      withInnerClasses(lcds) {
        lcds.foreach(traverse(_, ctx))
        traverse(body, ctx)
      }

    case LocalMethodInvocation(caller, method, tparams, tps, args) =>
      val lct = caller.getType.asInstanceOf[LocalClassType]
      val lcd = innerClasses(lct.id)
      val lmd = lcd.methods.find(_.id == method.id).get

      val subCtx = ctx.inGhost(lmd.flags contains Ghost)

      traverse(caller, subCtx)
      tps.foreach(traverse(_, subCtx))

      (lmd.params zip args) foreach { case (vd, arg) =>
        traverse(arg, subCtx.inGhost(vd.flags contains Ghost))
      }

    case LocalClassConstructor(ct, args) =>
      traverse(ct, ctx)
      val lcd = innerClasses(ct.id)

      (lcd.fields zip args).foreach { case (vd, arg) =>
        traverse(arg, ctx.inGhost(vd.flags contains Ghost))
      }

    case LocalClassSelector(expr, id, tpe) =>
      traverse(expr, ctx)
      traverse(id, ctx)
      traverse(tpe, ctx)

    case _ => super.traverse(e, ctx)
  }
}

