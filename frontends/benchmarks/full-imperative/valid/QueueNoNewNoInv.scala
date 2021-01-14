import stainless.lang._
import stainless.collection._
import stainless.lang.Option._
import stainless.annotation._

object Queue {  
  final case class Node(val value: BigInt, var nextOpt: Option[Node]) extends AnyHeapRef {}

  final case class Q(var first: Node,
                     var size: BigInt,
                     var last: Node,
                     var nodes: List[AnyHeapRef])
             extends AnyHeapRef {
 
    def enqueue(n: Node): Unit = {
      reads(Set(n, this))
      modifies(Set(n, this))
      n.nextOpt = Some(first)              
      first = n
      size = size + BigInt(1)
    }

    def dequeue: Option[BigInt] = {
      reads(Set(this, first))
      require(first.nextOpt != None())             
      modifies(Set(this))

      val wasFirst = first
      wasFirst.nextOpt match {
        case None() => None()
        case Some(nn) => {
          first = nn
          size = size - BigInt(1)
          Some(wasFirst.value)
        }
      }
    }              
  }
  
}
