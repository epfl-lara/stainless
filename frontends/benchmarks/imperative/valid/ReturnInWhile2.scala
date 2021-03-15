import stainless.annotation._
import stainless.lang._
import stainless.io._

object ReturnInWhile2 {
  def return10: Int = {
    while (true) {
      decreases(0)
      def f: Int = return 20
      return 10
    }
    assert(false)
    0
  }

  def return20: Int = {
    var x = 0
    while (true) {
      decreases(0)
      def f: Int = return 20
      x = f
      return x
    }
    assert(false)
    0
  }

  def tests: Unit = {
    assert(return10 == 10)
    assert(return20 == 20)
  }
}
