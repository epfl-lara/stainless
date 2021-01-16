import stainless.lang._

object ObjectNotInReads1Example {
  case class Node(var v: BigInt) extends AnyHeapRef

  def read(n1: Node, n2: Node): BigInt = {
    reads(Set(n1))
    n2.v
  }
}
