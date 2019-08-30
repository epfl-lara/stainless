import stainless.lang._

object SuperCalls {

  abstract class A {
    def bar: BigInt = 41
  }

  abstract class B extends A

  abstract class C extends B {
    override def bar: BigInt = super.bar + 1
  }

  case class D() extends C {
    override def bar: BigInt = super.bar * 10
  }

  def prop = {
    D().bar == 420
  }.holds

}
