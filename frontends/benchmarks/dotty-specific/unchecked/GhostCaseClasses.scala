// FIXME: Propagate ghost annotation

import stainless.lang._
import stainless.annotation._

object GhostCaseClasses {

  sealed trait GhostList
  case class GhostCons(@ghost val head: BigInt, @ghost tail: GhostList) extends GhostList
  case class GhostNil() extends GhostList

  def patmatch(): Unit = {
    val x = GhostCons(BigInt(10), GhostCons(BigInt(2), GhostNil()))

    x match {
      case GhostCons(x, GhostCons(y, t)) =>
        val foo = x // error: x is ghost
        val bar = y // error: y is ghost
        val baz = t // error: t is ghost
        ()

      case _ =>
        ()
    }
  }
}
