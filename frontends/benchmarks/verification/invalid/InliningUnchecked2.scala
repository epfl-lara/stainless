object InliningUnchecked2 {
  @inline def nonNegative(x: Int): Boolean = x >= 0

  def test: Int = {
    -10
  }.ensuring(nonNegative _)
}
