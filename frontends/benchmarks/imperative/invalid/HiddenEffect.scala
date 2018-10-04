trait HiddenEffect {
  var x: BigInt

  def f(): BigInt

  def g() = {
    val x0 = x
    f()
    assert(x == x0)
  }
}
