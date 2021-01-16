import stainless.lang._

object ObjectNotInModifies1Example {
  case class Node(var v: BigInt) extends AnyHeapRef

  def write(n1: Node, n2: Node): Unit = {
    reads(Set(n1, n2))
    modifies(Set(n1))
    n2.v = BigInt(123)
  }
}
