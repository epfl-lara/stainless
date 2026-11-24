import stainless.lang._

// The exceptions of `stainless.lang` take a message, which is empty by default.
object ExceptionMessages {
  case class Empty() extends Exception
  case class Coded(code: BigInt) extends IllegalStateException("coded")

  def describe(x: BigInt): String = {
    require(x >= 0)
    try {
      if (x == 0) throw new IllegalArgumentException("zero")
      if (x == 1) throw Coded(1)
      if (x == 2) throw Empty()
      "none"
    } catch {
      case e: IllegalArgumentException => e.getMessage
      case e: Coded => e.getMessage
      case e: Exception => e.getMessage
    }
  }.ensuring(res =>
    (x == 0 ==> (res == "zero")) &&
    (x == 1 ==> (res == "coded")) &&
    (x == 2 ==> (res == ""))
  )

  def helper(): Boolean = { Exception("helper").getMessage == "helper" }.holds
}
