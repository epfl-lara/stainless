
object TypeMembers4 {

  trait A
  case class B(value: Int) extends A {
    require(value > 0)
  }
  case class C() extends A

  abstract class Foo {
    type Bar <: A
    def x: Bar
  }

  case class SomeFoo() {
    type Bar = B
    def x: Bar = B(42)
  }

  def test(sf: SomeFoo) = {
    assert(sf.x.value == 42)
  }

  def test2(sf: SomeFoo)(n: sf.Bar) = {
    assert(n.value > 0)
  }

}
