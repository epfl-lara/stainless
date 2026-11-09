object i667:

  def f1(x: Int): Unit =
    BigInt(x)

  def f2(x: Int): Unit = {
    ()
  } ensuring { _ =>
    val y: BigInt = BigInt(x)
    true
  }
