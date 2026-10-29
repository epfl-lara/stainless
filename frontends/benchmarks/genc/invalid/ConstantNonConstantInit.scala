import stainless.annotation._

// The initial value of a global must be a constant expression in C, which a function call is not.
object ConstantNonConstantInit {

  def compute(n: Int): Int = n * 2

  val Table: Int = compute(21)

  @cCode.`export`
  def get(): Int = Table

}
