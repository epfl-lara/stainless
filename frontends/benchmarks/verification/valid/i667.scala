object i667:

  def f1(x: Int): Unit =
    BigInt(x)

  def f2(x: Int): Unit = {
    ()
  } ensuring { _ =>
    val y: BigInt = BigInt(x)
    true
  }

  def inEnsuringReceiver(x: Int): BigInt = {
    BigInt(x)
  } ensuring (_ == BigInt(x))

  def inRequireAndAssert(x: Int): Unit =
    require(BigInt(x) == BigInt(x))
    assert(BigInt(x) == BigInt(x))
