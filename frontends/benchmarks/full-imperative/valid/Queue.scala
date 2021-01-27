import stainless.lang._
import stainless.collection._
import stainless.lang.Option._
import stainless.annotation._
import stainless.collection.List._
import stainless.proof._

object Queue {
  final case class Node(val value: BigInt, var nextOpt: Option[Node]) extends AnyHeapRef {
  }

  final case class Q(var first: Node,
                     var size: BigInt,
                     var last: Node,
                     var asList: List[Node],
                     var rep: Set[AnyHeapRef])
             extends AnyHeapRef
  {
    // first node is not used, tis only a sentinel

    def valid: Boolean = {
      reads(rep ++ Set(this))
      size >= 0 && size == asList.size &&      
      rep.contains(first) && rep.contains(last) &&
      (asList match {
        case Nil() => first == last && first.nextOpt == None[Node]()
        case Cons(h, ns) =>
          first.nextOpt == Some(asList.head) &&
          asList.last == last
      }) && inv(asList, first)
    }

    def inv(nodes: List[Node], current: Node): Boolean = {
      reads(rep ++ Set(this))
      decreases(nodes.size)
      
      rep.contains(current) &&
      (nodes match {
        case Nil() => current.nextOpt == None[Node]() && current == last
        case n :: nodes1 =>
          current.nextOpt match {
            case None() => false
            case Some(n1) => n1 == n && inv(nodes1, n)
          }
      })
    }
  
    def enqueue(n: Node): Unit = {
      require(!rep.contains(n) && valid)
      reads(rep ++ Set(this, last, n))
      modifies(Set(this, last))

      last.nextOpt = Some(n)
      last = n
      size = size + 1
      asList = asList :+ n
      rep = rep ++ Set[AnyHeapRef](n)
    } ensuring (_ => asList == old(asList) :+ n)

    def dequeue: Node = {
      reads(rep ++ Set(this, first, first.nextOpt.get))
      require(size > 0 && valid)
      modifies(Set(this))

      first.nextOpt match {
        case Some(nn) => {
          check(nn == asList.head)
          first = nn
          size = size - 1
          asList = asList.tail
          nn
        }
      }
    } ensuring ((res:Node) => 
                asList == old(asList).tail &&
                res == old(asList).head)
  }
  
  @extern
  def main(args: Array[String]): Unit = {
    val n = Node(-1, None[Node]())
    val q = Q(n, 0, n, List[Node](), Set[AnyHeapRef]())
    q.enqueue(Node(5, None[Node]()))
    q.enqueue(Node(10, None[Node]()))
    q.enqueue(Node(14, None[Node]()))
    println(q.dequeue)
    println(q.dequeue)
    println(q.dequeue)
  }
}
