trait PureMethods {
  def f(): BigInt

  def g() = {
    val a = f()
    val b = f()
    assert(a == b)
  }
}
