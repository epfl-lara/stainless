import stainless.lang._
import stainless.annotation._

object HeadTraversalRead {
  sealed abstract class Node
  case class Cons(var v: BigInt, var next: Node) extends Node
  case class Nil() extends Node

  @extern
  def make(): Node = ???

  def f(n: BigInt): Unit = {
    val head = make()
    var cur: Node = head
    var sum = BigInt(0)
    var i = BigInt(0)
    while (i < n && cur.isInstanceOf[Cons]) {
      decreases(n - i)
      sum = sum + cur.asInstanceOf[Cons].v
      cur = cur.asInstanceOf[Cons].next
      i = i + 1
    }

    assert(head.isInstanceOf[Cons] || head.isInstanceOf[Nil])
  }
}
