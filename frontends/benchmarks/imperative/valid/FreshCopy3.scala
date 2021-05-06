import stainless.lang._
import stainless.annotation._

sealed case class S(var field: Int)

object FreshCopy2 {

  @pure
  def setField(arg: S): S = {
    var v = freshCopy(arg)
    v.field = 456
    v
  }

  def main() = {
    val s  = S(123)
    val s2 = setField(s)
    assert(s.field == 123)
    assert(s2.field == 456)

    s.field = 789
    assert(s.field == 789)
    assert(s2.field == 456)

    s2.field = 1000
    assert(s.field == 789)
    assert(s2.field == 1000)
  }
}
