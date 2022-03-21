import stainless.lang._
import stainless.annotation._

object i933 {
  def f() = {
    var i = 0
    val a = Array.fill(10) { i += 1; i }
    assert(i == 1)
    assert(a(4) == 1)
  }
}