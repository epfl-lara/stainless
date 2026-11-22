import stainless.lang._

object ConcreteLocalParents {
  class C(val x: BigInt) {
    def m: BigInt = x + 1
  }

  def localSubclass(k: BigInt): BigInt = {
    case class D(y: BigInt) extends C(y + k) {
      override def m: BigInt = y
    }
    val d: C = D(3)
    assert(d.x == 3 + k)
    assert(d.m == 3)
    d.x
  }.ensuring(_ == 3 + k)

  def anonymousSubclass(k: BigInt): BigInt = {
    val c = new C(k) { override def m: BigInt = 0 }
    assert(c.x == k)
    c.m
  }.ensuring(_ == 0)

  def localParent(k: BigInt): BigInt = {
    class A(val x: BigInt) {
      def double: BigInt = 2 * x
    }
    case class B(y: BigInt) extends A(y + k)
    assert(new A(1).double == 2)
    assert(B(1).double == 2 + 2 * k)
    B(1).x
  }.ensuring(_ == 1 + k)
}
