import stainless.lang.*

object i583b:

  type Pos = {i: BigInt with i > 0}

  def getMinusOne(o: Option[Pos]): BigInt = {
    o match
      case Some(x) => x - 1
      case None() => BigInt(1)
  }.ensuring(_ > 0)
