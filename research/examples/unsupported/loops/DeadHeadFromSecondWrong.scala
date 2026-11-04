import stainless.lang._

object DeadHeadFromSecondWrong {
  sealed abstract class Node
  case class Cons(var v: BigInt, var next: Node) extends Node
  case class Nil() extends Node

  def make(): Node = Cons(0, Cons(1, Cons(2, Nil())))

  def f(n: BigInt): Unit = {
    val head = make()
    if (head.isInstanceOf[Cons]) {
      var cur = head.asInstanceOf[Cons].next
      var i = BigInt(0)
      while (i < n && cur.isInstanceOf[Cons] && cur.asInstanceOf[Cons].next.isInstanceOf[Cons]) {
        decreases(n - i)
        val previous = cur.asInstanceOf[Cons]
        cur = previous.next

        cur.asInstanceOf[Cons].v = 1

        assert(previous.next.asInstanceOf[Cons].v == 2)
        i = i + 1
      }
    }
  }
}
