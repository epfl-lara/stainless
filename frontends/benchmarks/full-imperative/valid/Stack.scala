import stainless.lang._
import stainless.collection._
import stainless.lang.Option._
import stainless.annotation._
import stainless.proof._
import stainless.lang.StaticChecks._

object Stack {
  final case class Node(val value: BigInt, var nextOpt: Option[Node]) extends AnyHeapRef {}

  final case class Q(var first: Option[Node],
                     @ghost var size: BigInt,
                     @ghost var nodes: List[AnyHeapRef])
             extends AnyHeapRef
  {
    // first is a sentinel node, not stored in nodes
    
    @ghost
    def valid: Boolean = {      
      reads(nodes.content ++ Set(this))
      size == nodes.size &&
      inv(nodes, first)
    }

    @ghost
    def inv(nodesLeft: List[AnyHeapRef], current: Option[Node]): Boolean = {
      reads(nodesLeft.content ++ Set(this))
      decreases(nodesLeft.size)
      
      nodesLeft match {
        case Cons(hh, tail) => {
          hh.isInstanceOf[Node] &&
          ({
            val h = hh.asInstanceOf[Node]
            current == Some(h)  &&  inv(tail, h.nextOpt)
          })
        }
        case Nil() => current==None()
      }
    }    
  
    def push(n: Node): Unit = {
      reads(nodes.content ++ Set(this))
      require(valid && !nodes.contains(n))
      modifies(Set(this))

      n.nextOpt = first
      first = Some(n)
      nodes = n :: nodes 
      size = size + 1
    } ensuring (_ => valid)

    def pop: BigInt = {
      reads(nodes.content ++ Set(this))
      require(valid && !nodes.isEmpty)
      modifies(Set(this))

      val n = first.get
      first = n.nextOpt
      size = size - 1
      nodes = nodes.tail
      n.value
    } ensuring (_ => valid)
  }

  @extern
  def main(args: Array[String]): Unit = {
    val n = Node(-1, None[Node]())
    val s = Q(None[Node], 0, List[AnyHeapRef]())
    println("Stack with nodes")
    s.push(Node(5, None[Node]()))
    s.push(Node(10, None[Node]()))    
    s.push(Node(14, None[Node]()))
    println(s)
  }
  
}
