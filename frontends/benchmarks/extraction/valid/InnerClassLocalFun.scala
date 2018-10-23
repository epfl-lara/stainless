import stainless.lang._

object InnerClassLocalFun {

  abstract class Test {
    def something: BigInt
  }

  def foo(x: Boolean, l: BigInt): Test = {
    def bar(y: Boolean, m: BigInt): Test = {
      case class Bar() extends Test {
        def something = if (x && y) l else m
      }
      Bar()
    }
    bar(true, 3)
  }

  def test = (foo(true, 42).something == 42).holds
}
