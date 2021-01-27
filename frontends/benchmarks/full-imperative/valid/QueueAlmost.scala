import stainless.lang._
import stainless.collection._
import stainless.lang.Option._
import stainless.annotation._
import stainless.collection.List._

object QueueAlmost {
  final case class Node(val value: BigInt, var nextOpt: Option[Node]) extends AnyHeapRef {}

  final case class Q(private var first: Node,
                     private var size: BigInt,
                     private var last: Node,
                     private var asList: List[Node])
             extends AnyHeapRef
  {

    def getList: List[Node] = {
      require(valid)
      reads(Set(this))
      asList
    }
  
    def valid: Boolean = {
      reads(Set(this))
      size >= 0 && size == asList.size
    }

    // first node is not used

    def enqueue(n: Node): Unit = {
      require(!getList.content.contains(n) && valid)
      reads(Set(this, last))
      modifies(Set(this, last))

      last.nextOpt = Some(n)
      last = n
      size = size + 1
      asList = asList :+ n
    } ensuring (_ => valid && getList == old(getList) :+ n)

    def dequeue: Option[BigInt] = {
      reads(Set(this, first, first.nextOpt.get))
      require(first.nextOpt != None() && size > 0 && valid)
      modifies(Set(this))

      first.nextOpt match {
        case Some(nn) if size > 0 => {
          first = nn
          size = size - 1
          asList = asList.tail
          Some(nn.value)
        }
        case _ => None[BigInt]()
      }
    } ensuring ((res:Option[BigInt]) => valid &&
                getList == old(getList).tail)
  }

  @extern
  def main(args: Array[String]): Unit = {
    val n = Node(-1, None[Node]())
    val q = Q(n, 0, n, List[Node]())
    q.enqueue(Node(5, None[Node]()))
    q.enqueue(Node(10, None[Node]()))
    q.enqueue(Node(14, None[Node]()))
    println(q.dequeue.get)
    println(q.dequeue.get)
    println(q.dequeue.get)
  }

}
