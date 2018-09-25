/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package utils

import scala.collection.mutable.{HashSet => MutableHashSet}

import inox.utils.{Position, NoPosition}

object DebugSectionPositions extends inox.DebugSection("positions")

/** Inspect trees, detecting missing positions. */
trait PositionChecker extends ExtractionPipeline {

  val name: String
  val underlying: ExtractionPipeline

  override val s: underlying.s.type = underlying.s
  override val t: underlying.t.type = underlying.t
  override val context = underlying.context

  implicit val debugSection = DebugSectionPositions

  val phases = context.options.findOption(optDebugPhases)

  // We print debug output for this phase only if the user didn't specify
  // any phase with --debug-phases, or gave the name of (or a string
  // contained in) this phase
  lazy val debug = phases.isEmpty || (phases.isDefined && phases.get.exists(name.contains _))

  // Moreover, we only print when the corresponding debug sections are active
  lazy val debugPos: Boolean = debug && context.reporter.debugSections.contains(debugSection)

  override def invalidate(id: Identifier) = underlying.invalidate(id)

  object traverser extends t.TreeTraverser { self =>
    import t._

    override def traverse(fd: FunDef): Unit = {
      if (!fd.flags.contains(Synthetic)) super.traverse(fd)
    }

    override def traverse(e: Expr): Unit = {
      if (!e.getPos.isDefined) {
        context.reporter.debug(NoPosition, s"After $name: Missing position for expression '$e' (of type ${e.getClass}).")
      }

      super.traverse(e)
    }
  }

  def extract(symbols: s.Symbols): t.Symbols = {
    val result = underlying.extract(symbols)
    if (debugPos) result.functions.values foreach traverser.traverse
    result
  }

}

object PositionChecker {
  def apply(nme: String, pipeline: ExtractionPipeline): ExtractionPipeline {
    val s: pipeline.s.type
    val t: pipeline.t.type
  } = new {
    override val underlying: pipeline.type = pipeline
  } with PositionChecker {
    override val name: String = nme
  }
}
