object TypedHoleInferredNothing {
  def b: Boolean = ???
  def f = assert(b)
}
