import stainless.lang._
import stainless.collection._
import stainless.lang.Option._
import stainless.annotation._

object Queue {
  final case class Node(val value: BigInt, var nextOpt: Option[Node]) extends AnyHeapRef {}

  final case class Q(var first: Node,
                     var size: BigInt,
                     var last: Node)
             extends AnyHeapRef
  {

    def valid: Boolean = {
      reads(Set(this))
      size >= 0
    }

    // first node is not used
  
    def enqueue(n: Node): Unit = {
      reads(Set(this))
      require(valid)
      modifies(Set(this, last))

      last.nextOpt = Some(n)
      last = n
      size = size + 1
    } ensuring (_ => valid)

    def dequeue: Option[BigInt] = {
      reads(Set(this, first, first.nextOpt.get))
      require(first.nextOpt != None() && size > 0)
      modifies(Set(this))

      first.nextOpt match {
        case Some(nn) if size > 0 => {
          first = nn
          size = size - 1
          Some(nn.value)
        }
        case _ => None[BigInt]()
      }
    } ensuring ((res:Option[BigInt]) => valid)
  }

  @extern
  def main(args: Array[String]): Unit = {
    val n = Node(-1, None[Node]())
    val q = Q(n, 0, n)
    q.enqueue(Node(5, None[Node]()))
    q.enqueue(Node(10, None[Node]()))    
    q.enqueue(Node(14, None[Node]()))
    println(q.dequeue.get)
    println(q.dequeue.get)
    println(q.dequeue.get)
  }
  
}
