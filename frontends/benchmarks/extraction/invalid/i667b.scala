import stainless.lang.StaticChecks.*

object i667b:

  def inPostcondition(s: String): Unit = {
    ()
  }.ensuring { _ =>
    val y: BigInt = BigInt(s)
    true
  }

  def inEnsuringReceiver(s: String): BigInt = {
    BigInt(s)
  }.ensuring(_ == 0)

  def objectMethodInEnsuringReceiver(a: AnyRef, b: AnyRef): Boolean = {
    a eq b
  }.ensuring(_ => true)
