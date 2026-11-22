import stainless.lang._

object MemberClassTypePatterns {
  trait Lang {
    abstract class Node
    case class Leaf(w: BigInt) extends Node
  }

  // The leaf may belong to another instance of `Lang`
  def isNode(l1: Lang, l2: Lang): Unit = {
    val n: Any = l2.Leaf(1)
    assert(n match {
      case _: l1.Node => true
      case _ => false
    })
  }
}
