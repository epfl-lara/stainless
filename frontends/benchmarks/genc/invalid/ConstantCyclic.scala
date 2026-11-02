import stainless.annotation._

// Constants defined in terms of each other have no value in C (and would make their inlining loop).
object ConstantCyclic {

  val A: Int = B + 1

  val B: Int = A + 1

  @cCode.`export`
  def get(): Int = A

}
