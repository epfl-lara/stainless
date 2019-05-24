
object TypeMembers3 {

  trait A
  case class B(value: Int) extends A
  case class C() extends A

  abstract class Foo {
    type Bar <: A
    def x: Bar
  }

  case class SomeFoo() extends Foo {
    type Bar = B
    def x: Bar = B(42)
  }

  def test1(f: Foo) = {
    assert(f.x.isInstanceOf[A])
  }

  def test2(sf: SomeFoo) = {
    assert(sf.x.value == 42)
  }

}
