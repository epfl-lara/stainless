
object RefinedTypeMember {

  abstract class Foo {
    type Bar
    def x: Bar
  }

  case class SomeFoo() {
    type Bar = { y: Int => y > 0 }

    def x: Bar = 42
  }

  def test(sf: SomeFoo) = {
    assert(sf.x == 42)
  }

  def test2(sf: SomeFoo, n: sf.Bar) = {
    assert(n > 0)
  }

}
