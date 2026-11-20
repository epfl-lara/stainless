import stainless.lang._

object SwapVarRowReceiver {
  def f(m: Array[Array[BigInt]]): Unit = {
    require(m.length > 3 && m(1).length > 2 && m(2).length > 2)
    require(m(1)(0) == 10 && m(1)(1) == 11 && m(2)(0) == 20 && m(2)(1) == 21)
    var ii = 1
    swap(m(ii), {
      ii += 1
      0
    }, m(1), 1)
    assert(m(1)(0) == 11 && m(1)(1) == 10)
  }
}
