
object ShiftBeyondWidth {

  def f(x: Int): Unit = {
    require(x == 33)
    assert((1 << x) == 0) // false on the JVM: 1 << 33 == 2
  }

}
