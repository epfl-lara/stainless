trait ImpureMethods {
  var x: BigInt

  def f(): BigInt

  def g() = {
    val a = f()
    val b = f()
    assert(a == b)
  }
}
