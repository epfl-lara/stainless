import stainless.annotation._

// Top-level `val`s of mutable types are rejected (by Stainless itself): they would be global mutable state.
object ConstantMutable {

  case class Counter(var n: Int)

  val C: Counter = Counter(0)

  @cCode.`export`
  def get(): Int = C.n

}
