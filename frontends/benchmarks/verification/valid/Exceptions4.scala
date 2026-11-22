import stainless.lang._

case class FillError(code: BigInt) extends Exception

object Exceptions4 {
  // Mutation of an array in a try body
  def fill(a: Array[Int], n: Int): Unit = {
    require(a.length > 10 && 0 <= n && n < 5)
    try {
      a(0) = n
      if (n == 3) throw FillError(3)
      a(1) = n
    } catch {
      case FillError(_) => a(1) = 42
    }
  }.ensuring(_ => a(0) == n && (a(1) == n || a(1) == 42))
}
