import stainless.lang._
import stainless.collection._
import stainless.lang.Option._
import stainless.annotation._
import stainless.proof.check
import stainless.lang.StaticChecks._

object StackExample {
  final case class Node(val value: BigInt, var nextOpt: Option[Node]) extends AnyHeapRef {}

  final case class Q(var first: Option[Node],
                     @ghost var nodes: List[AnyHeapRef])
             extends AnyHeapRef
  {
    @ghost
    def valid: Boolean = {
      reads(nodes.content ++ Set(this))
      !nodes.contains(this) &&
      inv(nodes, first)
    }

    @ghost
    def inv(nodesLeft: List[AnyHeapRef], current: Option[Node]): Boolean = {
      reads(nodesLeft.content)
      decreases(nodesLeft.size)

      nodesLeft match {
        case Cons(hh, tail) => {
          hh.isInstanceOf[Node] &&
          {
            val h = hh.asInstanceOf[Node]
            current == Some(h) && inv(tail, h.nextOpt)
          }
        }
        case Nil() => current == None[Node]()
      }
    }

    def push(n: Node): Unit = {
      reads(nodes.content ++ Set(this, n))
      modifies(Set(this, n))
      require(valid && !nodes.contains(n))

      n.nextOpt = first
      first = Some(n)
      nodes = n :: nodes
    } ensuring { _ => valid && nodes == n :: old(nodes) }

    def pop: BigInt = {
      reads(nodes.content ++ Set(this))
      require(valid && !nodes.isEmpty)
      modifies(Set(this))

      val n = first.get
      first = n.nextOpt
      nodes = nodes.tail
      n.value
    } ensuring { _ => valid && nodes == old(nodes.tail) }
  }

  @extern
  def main(args: Array[String]): Unit = {
    val n = Node(-1, None[Node]())
    val s = Q(None[Node](), List[AnyHeapRef]())
    println("Stack with nodes")
    s.push(Node(5, None[Node]()))
    s.push(Node(10, None[Node]()))
    s.push(Node(14, None[Node]()))
    println("Stack is: " + s)
    println(s.pop)
    println(s.pop)
    println(s.pop)
    println("Stack is: " + s)
  }
}
