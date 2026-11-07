import stainless.lang._

object PrevCur {
  sealed abstract class Node
  case class Cons(var v: BigInt, var next: Node) extends Node
  case class Nil() extends Node

  def make(): Node = Cons(0, Cons(1, Cons(2, Nil())))

  def f(n: BigInt): Unit = {
    var prev: Node = make()
    var cur: Node = prev
    var i = BigInt(0)
    while (i < n && cur.isInstanceOf[Cons]) {
      decreases(n - i)
      prev = cur
      cur = cur.asInstanceOf[Cons].next

      prev.asInstanceOf[Cons].v = 5

      assert(prev.asInstanceOf[Cons].v == 5)
      i = i + 1
    }
  }
}
