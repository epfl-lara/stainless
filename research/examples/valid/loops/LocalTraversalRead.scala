import stainless.lang._

object LocalTraversalRead {
  sealed abstract class Node
  case class Cons(var v: BigInt, var next: Node) extends Node
  case class Nil() extends Node

  def make(): Node = Cons(0, Cons(1, Cons(2, Nil())))

  def f(n: BigInt): BigInt = {
    var cur: Node = make()
    var sum = BigInt(0)
    var i = BigInt(0)
    while (i < n && cur.isInstanceOf[Cons]) {
      decreases(n - i)
      sum = sum + cur.asInstanceOf[Cons].v
      cur = cur.asInstanceOf[Cons].next
      i = i + 1
    }
    sum
  }
}
