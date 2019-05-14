// FIXME: Propagate erased (seems to be invalid Dotty code though)
import stainless.lang._

object ErasedTerms3 {

  sealed trait GhostList
  case class GhostCons(erased val head: BigInt, val tail: GhostList) extends GhostList
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
