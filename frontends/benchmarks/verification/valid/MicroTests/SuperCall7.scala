import stainless.lang._

// Super calls into a trait from a class whose only parent is that trait, where `super` has the
// type `Object & A` (and `Object & A & Product & Serializable` for a case class)
object SuperCall7 {
  trait A {
    def f(x: BigInt): BigInt = x
  }

  case class B() extends A {
    override def f(x: BigInt): BigInt = super.f(x) + 1
  }

  class C extends A {
    override def f(x: BigInt): BigInt = super.f(x) * 2
  }

  trait D extends A {
    override def f(x: BigInt): BigInt = super.f(x) + 10
  }

  case class E() extends D {
    override def f(x: BigInt): BigInt = super.f(x) + 100
  }

  def test(x: BigInt): Unit = {
    assert(B().f(x) == x + 1)
    assert((new C).f(x) == 2 * x)
    assert(E().f(x) == x + 110)
  }
}
