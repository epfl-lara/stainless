object Issue1483:
  class A

  val x1 = new A
  val x2 = new A
  val ok = x1 == x2

  def testEq =
    assert(x1 == x2)

end Issue1483
