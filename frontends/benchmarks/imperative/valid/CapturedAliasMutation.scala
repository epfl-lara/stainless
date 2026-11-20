object CapturedAliasMutation {
  case class A(var x: BigInt)
  case class B(var a: A)

  def f(b: B): Unit = {
    def g(): Unit = {
      val y = b.a
      y.x = 1
    }
    g()
    assert(b.a.x == 1)
  }
}
