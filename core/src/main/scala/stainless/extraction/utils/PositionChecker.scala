/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package utils

import inox.utils.{Position, NoPosition}

object DebugSectionPositions extends inox.DebugSection("positions")

/** Inspect trees, detecting missing positions. */
trait PositionChecker { self: DebugPipeline =>

  final class PositionTraverser extends t.TreeTraverser { self =>
    import t._

    private var lastKnownPosition: Position = NoPosition

    override def traverse(fd: FunDef): Unit = {
      if (!fd.flags.contains(Synthetic)) {
        lastKnownPosition = NoPosition
        super.traverse(fd)
      }
    }

    override def traverse(e: Expr): Unit = {
      implicit val debugSection = DebugSectionPositions

      if (!e.getPos.isDefined) {
        context.reporter.debug(
          NoPosition,
          s"After $name: Missing position for expression '$e' (of type ${e.getClass})." +
          s"Last known position: $lastKnownPosition"
        )
      } else {
        lastKnownPosition = e.getPos
      }

      super.traverse(e)
    }
  }
}

