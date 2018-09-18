object LambdaMutation {
  def f() = {
    var x = 0
    val g = () => { x = x + 1 }
    g()
    assert(x == 1)
  }
}
