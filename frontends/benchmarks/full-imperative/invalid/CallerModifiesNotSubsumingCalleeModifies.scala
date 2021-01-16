import stainless.lang._

object CallerModifiesNotSubsumingCalleeModifiesExample {
  case class Node(var v: BigInt) extends AnyHeapRef

  def write1(n1: Node, n2: Node): Unit = {
    reads(Set(n1, n2))
    modifies(Set(n1, n2))
    n1.v = n2.v
    n2.v = n1.v
  }

  def write2(n1: Node, n2: Node): Unit = {
    reads(Set(n1, n2))
    modifies(Set(n1))
    write1(n1, n2)
  }
}
