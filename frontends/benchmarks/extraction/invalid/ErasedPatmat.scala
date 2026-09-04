package erased.patmat

import stainless.lang._

object ErasedPatmat {

  sealed trait ErasedList
  case class ErasedCons(erased val head: BigInt, val tail: ErasedList) extends ErasedList
  case class ErasedNil() extends ErasedList

  def patmatch(): Unit = {
    val x = ErasedCons(BigInt(10), ErasedCons(BigInt(2), ErasedNil()))

    x match {
      case ErasedCons(x, ErasedCons(y, t)) =>
        val foo = x // error: x is erased
        val bar = y // error: y is erased
        ()

      case _ =>
        ()
    }
  }
}
