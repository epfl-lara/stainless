import stainless.lang._

case class ArrayError(code: BigInt) extends Exception

object Exceptions4 {
  // Mutation of an array in a try body
  def fill(a: Array[Int], n: Int): Unit = {
    require(a.length > 10 && 0 <= n && n < 5)
    try {
      a(0) = n
      if (n == 3) throw ArrayError(3)
      a(1) = n
    } catch {
      case ArrayError(_) => a(1) = 42
    }
  }.ensuring(_ => a(0) == n && (a(1) == n || a(1) == 42))

  // Throws out of a loop in a throwing function
  def findNeg(a: Array[BigInt]): Int = {
    var i = 0
    (while (i < a.length) {
      decreases(a.length - i)
      if (a(i) < 0) throw ArrayError(a(i))
      i += 1
    }).invariant(0 <= i && i <= a.length)
    i
  }.ensuring(res => res == a.length).throwing {
    case ArrayError(c) => c < 0
    case _ => false
  }
}
