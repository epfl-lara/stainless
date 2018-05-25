/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package xlang

/** Inspect trees, detecting illegal structures. */
trait TreeSanitizer extends ExtractionPhase {
  val s: Trees
  val t: s.type
  import s._

  /** Throw a [[MissformedStainlessCode]] exception when detecting an illegal pattern. */
  override final def transform(symbols: s.Symbols): t.Symbols = {
    symbols.functions.values foreach checkPrecondition
    symbols
  }

  private sealed abstract class Action
  private case object Continue extends Action
  private case class ContinueWith(e: Expr) extends Action
  private case object Stop extends Action

  private def traverse(e: Expr)(visitor: Expr => Action): Unit = {
    def rec(f: Expr) = traverse(f)(visitor)
    visitor(e) match{
      case Stop => /* nothing */
      case ContinueWith(e) => rec(e)
      case Continue =>
        val Operator(es, _) = e
        es foreach rec
    }
  }

  /* This detects both multiple `require` and `require` after `decreases`. */

  private def checkPrecondition(fd: FunDef): Unit =
    checkPrecondition(fd.id, fd.fullBody)

  private def checkPrecondition(lfd: LocalFunDef): Unit =
    checkPrecondition(lfd.name.id, lfd.body.body)

  private def checkPrecondition(id: Identifier, body: Expr): Unit = {
    exprOps withoutSpecs body foreach { bareBody =>
      traverse(bareBody) {
        case e: Require =>
          throw MissformedStainlessCode(e, s"$id contains an unexpected `require`.")

        case e: Decreases =>
          throw MissformedStainlessCode(e, s"$id contains an unexpected `decreases`.")

        case e: LetRec =>
          // Traverse LocalFunDef independently
          e.fds foreach checkPrecondition
          ContinueWith(e.body)

        case e: Lambda =>
          checkPrecondition(FreshIdentifier("lambda"), e.body)
          Stop

        case _ => Continue
      }
    }
  }
}

object TreeSanitizer {
  def apply(trees: Trees)(implicit ctx: inox.Context): ExtractionPhase {
    val s: trees.type
    val t: trees.type
  } = new TreeSanitizer {
    override val s: trees.type = trees
    override val t: trees.type = trees
    override val context = ctx
  }
}
