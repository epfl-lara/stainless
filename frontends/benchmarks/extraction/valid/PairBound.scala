object PairBound {
  case class Pair[A](x: A, y: A)

  def makePair1[A, B >: A](x: A, y: B): Pair[B] = {
    Pair[B](x, y)
  }

  def makePair2[B, A <: B](x: A, y: B): Pair[B] = {
    Pair[B](x, y)
  }
}
