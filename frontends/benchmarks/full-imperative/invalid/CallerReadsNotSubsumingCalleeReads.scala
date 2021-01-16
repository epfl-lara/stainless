import stainless.lang._

object CallerReadsNotSubsumingCalleeReadsExample {
  case class Node(var v: BigInt) extends AnyHeapRef

  def read1(n1: Node, n2: Node): BigInt = {
    reads(Set(n1, n2))
    n1.v + n2.v
  }

  def read2(n1: Node, n2: Node): BigInt = {
    reads(Set(n1))
    read1(n1, n2)
  }
}
