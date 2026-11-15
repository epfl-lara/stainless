import stainless.lang._
import stainless.annotation._

object HeadTraversalWrite {
  sealed abstract class Node
  case class Cons(var v: BigInt, var next: Node) extends Node
  case class Nil() extends Node

  @extern
  def make(): Node = ???

  def f(n: BigInt): Unit = {
    val head = make()
    var cur: Node = head
    var i = BigInt(0)
    while (i < n && cur.isInstanceOf[Cons]) {
      decreases(n - i)
      cur.asInstanceOf[Cons].v = 4
      cur = cur.asInstanceOf[Cons].next
      i = i + 1
    }

    assert(head.isInstanceOf[Cons] || head.isInstanceOf[Nil])
  }
}
