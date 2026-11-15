import stainless.lang._

object GrowingListWrong {
  sealed abstract class Node
  case class Cons(var v: BigInt, var next: Node) extends Node
  case class Nil() extends Node

  def f(n: BigInt): Unit = {
    var cur: Node = Nil()
    var i = BigInt(0)
    while (i < n) {
      decreases(n - i)
      cur = Cons(0, cur)

      val c = cur.asInstanceOf[Cons]
      if (c.next.isInstanceOf[Cons] && c.next.asInstanceOf[Cons].next.isInstanceOf[Cons]) {
        val x = c.next.asInstanceOf[Cons].next.asInstanceOf[Cons]
        x.v = 5

        assert(cur.asInstanceOf[Cons].next.asInstanceOf[Cons].next.asInstanceOf[Cons].v == 0)
      }
      i = i + 1
    }
  }
}
