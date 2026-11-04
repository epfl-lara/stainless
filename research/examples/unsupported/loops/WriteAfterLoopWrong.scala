import stainless.lang._

object WriteAfterLoopWrong {
  sealed abstract class Node
  case class Cons(var v: BigInt, var next: Node) extends Node
  case class Nil() extends Node

  def make(): Node = Cons(0, Cons(1, Cons(2, Nil())))

  def f(n: BigInt): Unit = {
    var cur: Node = make()
    var i = BigInt(0)
    while (i < n && cur.isInstanceOf[Cons] && cur.asInstanceOf[Cons].next.isInstanceOf[Cons]) {
      decreases(n - i)
      cur = cur.asInstanceOf[Cons].next
      i = i + 1
    }

    if (cur.isInstanceOf[Cons]) {
      val before = cur.asInstanceOf[Cons].v

      cur.asInstanceOf[Cons].v = before + 1

      assert(cur.asInstanceOf[Cons].v == before)
    }
  }
}
