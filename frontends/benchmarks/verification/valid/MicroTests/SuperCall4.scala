
import stainless.lang._
import stainless.annotation._

object SuperCall4 {

  sealed abstract class Foo1 {
    def bar: BigInt = 41
  }

  sealed abstract class Foo2 extends Foo1 {
    override def bar: BigInt = super.bar + 1
  }

  case class Bar() extends Foo2 {
    override def bar: BigInt = super.bar * 10
  }

  def test1(bar: Bar) = {
    bar.bar == 420
  }.holds

  def test2(foo2: Foo2) = {
    foo2.bar == 42 || foo2.bar == 420
  }.holds

  def test3(foo1: Foo1) = {
    foo1.bar == 41 || foo1.bar == 42 || foo1.bar == 420
  }.holds

}
