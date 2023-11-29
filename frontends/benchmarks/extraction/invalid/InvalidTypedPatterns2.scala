object InvalidTypedPatterns2 {
  def test[A, B](a: A, b: B): Unit = {
    val (aa1: A, bb: A) = (a, b) // bb: A is invalid
  }
}