import stainless.lang._

object SuperCall3 {

  sealed abstract class A {
    def hello: BigInt = 1
  }

  case class B() extends A {
    override def hello = super.hello + 1
  }

  case class C() extends A {
    override def hello = super.hello + 2
  }

  def test1(x: A) = {
    if (x.isInstanceOf[B]) x.hello == 2
    else if (x.isInstanceOf[C]) x.hello == 3
    else x.hello == 1
  }.holds

  def test2 = {
    B().hello == 2
  }.holds

  def test3 = {
    C().hello == 3
  }.holds

}
