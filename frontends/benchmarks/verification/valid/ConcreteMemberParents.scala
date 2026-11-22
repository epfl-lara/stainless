import stainless.lang._

object ConcreteMemberParents {
  trait Lang {
    def base: BigInt
    class Node(val weight: BigInt) {
      def total: BigInt = weight + base
    }
    case class Leaf(w: BigInt) extends Node(w + 1) {
      override def total: BigInt = w
    }
    def mk(w: BigInt): Node = new Node(w)
    def leaf(w: BigInt): Node = Leaf(w)
  }
  case class L(base: BigInt) extends Lang

  def test(l: L): Unit = {
    assert(l.mk(3).weight == 3)
    assert(l.mk(3).total == 3 + l.base)
    assert(l.leaf(3).weight == 4)
    assert(l.leaf(3).total == 3)
  }
}
