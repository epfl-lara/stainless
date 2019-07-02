
object TypeMembers0 {

  sealed abstract class Foo {
    type Bar
    def x: Bar
  }

  case class SomeFoo() extends Foo {
    type Bar = Int
    def x: Bar = 42
  }

  def test(sf: SomeFoo) = {
    assert(sf.x == 42)
  }

}
