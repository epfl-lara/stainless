/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package xlang

/** Inspect trees, detecting illegal structures. */
trait TreeSanitizer extends ExtractionPipeline {
  val s: xlang.Trees
  val t: s.type
  import s._

  abstract class Visitor extends (FunDef => Unit) {
    def visit(fd: FunDef): Unit = visit(fd.id, fd.fullBody)
    def visit(lfd: LocalFunDef): Unit = visit(lfd.name.id, lfd.body.body)
    def visit(id: Identifier, body: Expr)

    final def apply(fd: FunDef): Unit = visit(fd)
  }

  /** Throw a [[MissformedStainlessCode]] exception when detecting an illegal pattern. */
  override final def extract(symbols: s.Symbols): t.Symbols = {
    symbols.functions.values foreach CheckPrecondition
    symbols.functions.values foreach CheckIgnoredFields(symbols)
    symbols
  }

  override final def invalidate(id: Identifier): Unit = ()

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
  private case object CheckPrecondition extends Visitor {
    override def visit(id: Identifier, body: Expr): Unit = {
      exprOps withoutSpecs body foreach { bareBody =>
        traverse(bareBody) {
          case e: Require =>
            throw MissformedStainlessCode(e, s"$id contains an unexpected `require`.")

          case e: Decreases =>
            throw MissformedStainlessCode(e, s"$id contains an unexpected `decreases`.")

          case e: LetRec =>
            // Traverse LocalFunDef independently
            e.fds foreach visit
            ContinueWith(e.body)

          case e: Lambda =>
            visit(FreshIdentifier("lambda"), e.body)
            Stop

          case _ => Continue
        }
      }
    }
  }

  /* This detects accesses to @ignored fields */
  private case class CheckIgnoredFields(symbols: Symbols) extends Visitor {
    private implicit val syms: Symbols = symbols

    override def visit(id: Identifier, body: Expr): Unit = {
      traverse(body) {
        case e @ ClassSelector(obj, selector) =>
          val ct = obj.getType.asInstanceOf[ClassType]
          ct.getField(selector) match {
            case None =>
              throw MissformedStainlessCode(e, s"Cannot find field `$selector` of class $ct.")
            case Some(field) if field.flags contains Ignore =>
              throw MissformedStainlessCode(e, s"Cannot access ignored field `$selector` from non-extern context.")
            case _ =>
              Continue
          }

        case e @ ClassConstructor(ct, args) =>
          ct.lookupClass match {
            case None =>
              throw MissformedStainlessCode(e, s"Cannot find class for type `$ct`.")

            case Some(tcd) if tcd.fields.exists(_.flags contains Ignore) =>
              val ignoredFields = tcd.fields.filter(_.flags contains Ignore).map(_.id).mkString(", ")
              throw MissformedStainlessCode(
                e,
                s"Cannot build an instance of a class with ignored fields in non-extern context" +
                s"($ct has ignored fields: $ignoredFields)."
              )

            case _ => Continue
          }

        case _ => Continue
      }
    }
  }

}

object TreeSanitizer {
  def apply(trees: Trees)(implicit ctx: inox.Context): ExtractionPipeline {
    val s: trees.type
    val t: trees.type
  } = new TreeSanitizer {
    override val s: trees.type = trees
    override val t: trees.type = trees
    override val context = ctx
  }
}
