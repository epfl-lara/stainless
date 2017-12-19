/* Copyright 2009-2017 EPFL, Lausanne */

package stainless
package extraction

import xlang.{ trees => xt }

/** Inspect trees, detecting illegal structures. */
object TreeSanitizer {

  import xt.exprOps
  import exprOps.Deconstructor

  /** Throw a [[MissformedStainlessCode]] exception when detecting an illegal pattern. */
  def check(program: Program { val trees: xt.type }): Unit = {
    val funs = program.symbols.functions.values
    funs foreach checkPrecondition
  }

  private sealed abstract class Action
  private case object Continue extends Action
  private case class ContinueWith(e: xt.Expr) extends Action
  private case object Stop extends Action

  private def traverse(e: xt.Expr)(visitor: xt.Expr => Action): Unit = {
    def rec(f: xt.Expr) = traverse(f)(visitor)
    visitor(e) match{
      case Stop => /* nothing */
      case ContinueWith(e) => rec(e)
      case Continue =>
        val Deconstructor(es, _) = e
        es foreach rec
    }
  }

  /* This detects both multiple `require` and `require` after `decreases`. */

  private def checkPrecondition(fd: xt.FunDef): Unit =
    checkPrecondition(fd.id, fd.fullBody)

  private def checkPrecondition(lfd: xt.LocalFunDef): Unit =
    checkPrecondition(lfd.name.id, lfd.body.body)

  private def checkPrecondition(id: Identifier, body: xt.Expr): Unit = {
    exprOps withoutSpecs body foreach { bareBody =>
      traverse(bareBody) {
        case e: xt.Require =>
          throw MissformedStainlessCode(e, s"$id contains an unexpected `require`.")

        case e: xt.Decreases =>
          throw MissformedStainlessCode(e, s"$id contains an unexpected `decreases`.")

        case e: xt.LetRec =>
          // Traverse LocalFunDef independently
          e.fds foreach checkPrecondition
          ContinueWith(e.body)

        case e: xt.Lambda =>
          checkPrecondition(FreshIdentifier("lambda"), e.body)
          Stop

        case _ => Continue
      }
    }
  }

}

