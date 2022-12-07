object i1352 {
  case class Test(val smth: Int, val other: Int) {
    def this(smth: Int) = this(smth, 42)
  }

  def test(x: Int) = {
    val t = new Test(x)
  }
}