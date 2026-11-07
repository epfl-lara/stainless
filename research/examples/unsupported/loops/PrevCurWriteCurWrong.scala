import stainless.lang._

object PrevCurWriteCurWrong {
  sealed abstract class Node
  case class Cons(var v: BigInt, var next: Node) extends Node
  case class Nil() extends Node

  def make(): Node = Cons(0, Cons(1, Cons(2, Nil())))

  def f(n: BigInt): Unit = {
    var cur: Node = make()
    var i = BigInt(0)
    while (i < n && cur.isInstanceOf[Cons] && cur.asInstanceOf[Cons].next.isInstanceOf[Cons]) {
      decreases(n - i)
      val prev = cur.asInstanceOf[Cons]
      val before = prev.next.asInstanceOf[Cons].v
      cur = prev.next

      cur.asInstanceOf[Cons].v = before + 1

      assert(prev.next.asInstanceOf[Cons].v == before)
      i = i + 1
    }
  }
}
