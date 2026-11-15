import stainless.lang._
import stainless.annotation._

object PreResolvedCursorExtern {
  sealed abstract class Node
  case class Cons(var v: BigInt, var next: Node) extends Node
  case class Nil() extends Node

  @extern
  def make(): Node = ???

  def f(n: BigInt): Unit = {
    var cur: Node = make()
    if (cur.isInstanceOf[Cons] && cur.asInstanceOf[Cons].next.isInstanceOf[Cons]) {
      cur.asInstanceOf[Cons].next.asInstanceOf[Cons].v = 10
    }

    var i = BigInt(0)
    while (i < n && cur.isInstanceOf[Cons]) {
      decreases(n - i)
      val c = cur.asInstanceOf[Cons]

      c.v = 7

      assert(c.v == 7)
      cur = c.next
      i = i + 1
    }
  }
}
