import stainless.annotation._

object LastDynAssert {
  @extern
  def dynAssert(cond: Boolean): Unit = {
    (??? : Unit)
  } ensuring(cond)

  def f() = {
    dynAssert(false) 
    (dynAssert(false), 0)
    assert(false)
  }
}
