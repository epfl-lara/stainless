
import stainless.lang._
// import stainless.collection._

object AnonymousClasses1 {

  abstract class Foo {
    def bar: Int
  }

  def level1(x: Int) = {
    def level2(y: Int) = {
      case class Level3(z: Int) {
        def makeFoo(a: Int) = {
          new Foo {
            def bar = x + y + z + a
          }
        }
      }
      val level3 = Level3(y + 1)
      level3.makeFoo(100)
    }
    level2(x + 1)
  }

  def test(x: Int) = {
    require(x >= 0 && x < 100)
    def go(n: Int): Int = {
      require(n >= 0)
      if (n == 0) n else go(n - 1)
    }

    def makeFoo(m: Int) = {
      require(m == 0)
      new Foo {
        def bar = m + x
      }
    }

    makeFoo(go(x + 1))
  }

  def theorem = {
    test(20).bar == 20
  }.holds

}
