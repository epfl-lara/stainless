object i667d:

  def f(i: BigInt): BigInt =
    i

  def inPostcondition(i: Int): Unit = {
    ()
  } ensuring { _ =>
    f(i) == 0
  }
