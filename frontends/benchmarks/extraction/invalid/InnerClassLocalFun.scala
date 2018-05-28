import stainless.lang._

object InnerClassLocalFun {

  abstract class Test {
    def something: BigInt
  }

  def foo(x: Boolean, l: BigInt): Test = {
    require(l > 1)
    case class Foo() extends Test {
      def something = {
        def bar(y: Boolean, m: BigInt): Test = {
          require(m > 2)
          case class Bar() extends Test {
            def something = {
              def baz(z: Boolean, o: BigInt): Test = {
                require(o > 3)
                case class Baz(a: Boolean, b: Boolean, c: Boolean) extends Test {
                  def something: BigInt = if (a) l else if (b) m else if (c) o else 0
                }
                Baz(x, y, z)
              }
              baz(false, 4).something
            }
          }
          Bar()
        }
        bar(true, 3).something
      }
    }
    Foo()
  }

  def test = (foo(false, 2).something == 3).holds
}
