object i667a:

  def inBody(s: String): BigInt =
    BigInt(s)

  def inPostcondition(s: String): Unit = {
    ()
  } ensuring { _ =>
    val y: BigInt = BigInt(s)
    true
  }

  def inEnsuringReceiver(s: String): BigInt = {
    BigInt(s)
  } ensuring (_ == 0)

  def inRequire(s: String): Unit =
    require(BigInt(s) == 0)

  def inLambdaInPostcondition(s: String): Unit = {
    ()
  } ensuring { _ =>
    ((t: String) => BigInt(t) == 0)(s)
  }

  def ifInEnsuringReceiver: BigInt = {
    BigInt(if true then 0 else 1)
  } ensuring (_ == 0)

  def objectMethodInPostcondition(a: AnyRef, b: AnyRef): Unit = {
    ()
  } ensuring { _ =>
    a eq b
  }

  def objectMethodInEnsuringReceiver(a: AnyRef, b: AnyRef): Boolean = {
    a eq b
  } ensuring (_ => true)

  def scalaApiInPostcondition(x: Int): Unit = {
    ()
  } ensuring { _ =>
    val l = scala.collection.immutable.List(x)
    true
  }

  def scalaApiInEnsuringReceiver(x: Int): Int = {
    scala.collection.immutable.List(x).head
  } ensuring (_ == x)
