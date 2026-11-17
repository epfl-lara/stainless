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

  def ifInEnsuringReceiver: BigInt = {
    BigInt(if true then 0 else 1)
  } ensuring (_ == 0)

  def f(i: BigInt): BigInt =
    i

  def implicitConversionInBody(i: Int): BigInt = {
    f(i)
  } ensuring (_ == BigInt(i))

  def implicitConversionInPostcondition(i: Int): Unit = {
    ()
  } ensuring { _ =>
    f(i) == BigInt(i)
  }
