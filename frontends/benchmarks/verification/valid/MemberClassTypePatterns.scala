import stainless.lang._

object MemberClassTypePatterns {
  trait Lang {
    abstract class Node
    case class Leaf(w: BigInt) extends Node
  }
  case class L(n: BigInt) extends Lang

  def isNode(l: Lang, n: Any): Boolean = n match {
    case _: l.Node => true
    case _ => false
  }

  def weight(l: Lang, n: Any): BigInt = n match {
    case lf: l.Leaf => lf.w
    case _ => 0
  }

  def test(l: L): Unit = {
    assert(isNode(l, l.Leaf(1)))
    assert(!isNode(l, 1))
    assert(weight(l, l.Leaf(3)) == 3)
  }
}
