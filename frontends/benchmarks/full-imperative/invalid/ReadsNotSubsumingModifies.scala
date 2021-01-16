import stainless.lang._

object ReadsNotSubsumingModifiesExample {
  case class Node(var v: BigInt) extends AnyHeapRef

  def write(n: Node): Unit = {
    modifies(Set(n))
    n.v = 123
  }
}
