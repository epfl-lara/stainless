import stainless.lang._

object ObjectNotInReads2Example {
  case class Node(var v: BigInt) extends AnyHeapRef

  def read(n1: Node, n2: AnyHeapRef): Boolean = {
    reads(Set(n1))
    n2.isInstanceOf[Node]
  }
}
