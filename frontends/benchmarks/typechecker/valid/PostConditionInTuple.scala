import stainless.annotation._

object PostConditionInTuple {
  @extern
  def dynAssert(cond: Boolean): Unit = {
    (??? : Unit)
  } ensuring(cond)

  def f() = {
    (dynAssert(false), 0)
  } ensuring(_ => false)
}
