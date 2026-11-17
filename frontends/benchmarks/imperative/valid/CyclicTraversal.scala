import stainless.lang._

object CyclicTraversal {
  sealed abstract class Node
  case class Cons(var v: BigInt, var next: Node) extends Node
  case class Nil() extends Node

  def f(n: BigInt): Unit = {
    val c = Cons(0, Nil())
    c.next = c
    var cur: Node = c
    var i = BigInt(0)
    while (i < n && cur.isInstanceOf[Cons]) {
      decreases(n - i)

      cur.asInstanceOf[Cons].v = i

      assert(cur.asInstanceOf[Cons].next.asInstanceOf[Cons].v == i)
      cur = cur.asInstanceOf[Cons].next
      i = i + 1
    }
  }
}
