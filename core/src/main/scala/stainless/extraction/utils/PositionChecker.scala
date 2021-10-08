/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package utils

import inox.utils.{Position, NoPosition}

object DebugSectionPositions extends inox.DebugSection("positions")

/** Inspect trees, detecting missing positions. */
trait PositionChecker {
  val t: ast.Trees

  val name: String
  val context: inox.Context

  final class PositionTraverser extends t.ConcreteStainlessSelfTreeTraverser { self =>
    import t._

    given givenPopts: t.PrinterOptions = t.PrinterOptions.fromContext(context)
    given givenDebugSection: DebugSectionPositions.type = DebugSectionPositions

    private var lastKnownPosition: Position = NoPosition

    override def traverse(fd: FunDef): Unit = {
      if (fd.flags.contains(Synthetic)) {
        return ()
      }

      if (!fd.getPos.isDefined) {
        context.reporter.debug(
          NoPosition,
          s"After $name: Missing position for function '${fd.asString}'."
        )
      }

      lastKnownPosition = fd.getPos
      super.traverse(fd)
    }

    override def traverse(e: Expr): Unit = {
      if (!e.getPos.isDefined) {
        context.reporter.debug(
          NoPosition,
          s"After $name: Missing position for expression '${e.asString}' (of type ${e.getClass}). " +
          s"Last known position: $lastKnownPosition"
        )
      } else {
        lastKnownPosition = e.getPos
      }

      super.traverse(e)
    }

    override def traverse(tpe: Type): Unit = {
      if (!tpe.getPos.isDefined) {
        context.reporter.debug(
          NoPosition,
          s"After $name: Missing position for type '${tpe.getPos}' (of type ${tpe.getClass})." +
          s"Last known position: $lastKnownPosition"
        )
      } else {
        lastKnownPosition = tpe.getPos
      }

      super.traverse(tpe)
    }
  }
}

