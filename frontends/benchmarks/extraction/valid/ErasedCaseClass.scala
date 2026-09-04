package erased.caseclass

import stainless.lang._

object ErasedCaseClass {

  sealed trait ErasedList
  case class ErasedCons(erased var head: BigInt, val tail: ErasedList) extends ErasedList
  case class ErasedNil() extends ErasedList

  def patmatch(): Unit = {
    val x = ErasedCons(BigInt(10), ErasedCons(BigInt(2), ErasedNil()))

    x match {
      case gc @ ErasedCons(x, ErasedCons(y, t)) =>
        ghost(x)
        gc.head = BigInt(-1)

        ()

      case _ =>
        ()
    }
  }
}
