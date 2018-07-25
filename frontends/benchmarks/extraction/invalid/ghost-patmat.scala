import stainless.lang._
import stainless.annotation.ghost

sealed trait GhostList
case class GhostCons(@ghost val head: BigInt, val tail: GhostList) extends GhostList
case class GhostNil() extends GhostList

object GhostMethods {

  def patmatch(): Unit = {
    val x = GhostCons(BigInt(10), GhostCons(BigInt(2), GhostNil()))

    x match {
      case GhostCons(x, GhostCons(y, t)) =>
        val foo = x // error: x is ghost
        val bar = y // error: y is ghost
        ()

      case _ =>
        ()
    }
  }
}
