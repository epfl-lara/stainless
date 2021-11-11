package ghost.caseclass

import stainless.lang._
import stainless.annotation.{ghost => ghostAnnot}

object GhostCaseClass {

  sealed trait GhostList
  case class GhostCons(@ghostAnnot var head: BigInt, val tail: GhostList) extends GhostList
  case class GhostNil() extends GhostList

  def patmatch(): Unit = {
    val x = GhostCons(BigInt(10), GhostCons(BigInt(2), GhostNil()))

    x match {
      case gc @ GhostCons(x, GhostCons(y, t)) =>
        ghost(x)
        gc.head = BigInt(-1)

        ()

      case _ =>
        ()
    }
  }
}
