import stainless.lang._

object LocalTraversalWrong {
  sealed abstract class Node
  case class Cons(var v: BigInt, var next: Node) extends Node
  case class Nil() extends Node

  def make(): Node = Cons(0, Cons(1, Cons(2, Nil())))

  def f(n: BigInt): Unit = {
    var cur: Node = make()
    var i = BigInt(0)
    while (i < n && cur.isInstanceOf[Cons]) {
      decreases(n - i)
      val c = cur.asInstanceOf[Cons]

      c.v = 7

      assert(c.v == 8)
      cur = c.next
      i = i + 1
    }
  }
}
