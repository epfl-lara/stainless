import stainless.annotation.*
import stainless.collection.*
import stainless.lang.*

object i1024a:
  type T = BigInt

  @pure
  def listLength(l: List[T]): Int = {
    l match
      case head :: tl =>
        val tlLen: Int = listLength(tl)
        if tlLen < Int.MaxValue then tlLen + 1
        else 0
      case Nil() => 0
  }.ensuring(0 <= _)
