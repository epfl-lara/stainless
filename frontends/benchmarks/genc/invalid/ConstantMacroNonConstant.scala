import stainless.annotation._

// A macro is expanded in place, so a constant whose initial value refers to a macro is only a constant
// expression in C if the value of the macro is one as well, which a function call is not.
object ConstantMacroNonConstant {

  def compute(n: Int): Int = n * 2

  @cCode.define
  val N: Int = compute(21)

  val M: Int = N + 1

  @cCode.`export`
  def get(): Int = M

}
