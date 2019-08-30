trait VarUpdate {
  var x: BigInt

  def f() = {
    x = 0
    assert(x == 0)
  }
}
