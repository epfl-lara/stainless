import stainless.lang._

object ConcreteParents {
  class A(val n: BigInt) {
    def size: BigInt = n
  }
  case class B(k: BigInt) extends A(k - 1) {
    override def size: BigInt = k
  }

  // The subclasses of `A` may override `size`
  def sizeIsN(a: A): Unit = {
    assert(a.size == a.n)
  }

  def nIsK(b: B): Unit = {
    assert(b.n == b.k)
  }
}

object ConcreteLocalParents {
  def localParent(k: BigInt): BigInt = {
    class A(val x: BigInt)
    case class B(y: BigInt) extends A(y + k)
    B(1).x
  }.ensuring(_ == 1)
}
