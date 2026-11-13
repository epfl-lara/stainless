object i839d:

  case class B(a: Int = 0)

  def test =
    val b = B()
    42

  def defaultValue(): Unit =
    assert(B().a == 0)
