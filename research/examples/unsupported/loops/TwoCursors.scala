import stainless.lang._

object TwoCursors {
  sealed abstract class Node
  case class Cons(var v: BigInt, var next: Node) extends Node
  case class Nil() extends Node

  def make(): Node = Cons(0, Cons(1, Cons(2, Nil())))

  def f(n: BigInt): Unit = {
    var a: Node = make()
    var b: Node = make()
    var i = BigInt(0)
    while (i < n && a.isInstanceOf[Cons] && b.isInstanceOf[Cons]) {
      decreases(n - i)

      a.asInstanceOf[Cons].v = 1
      b.asInstanceOf[Cons].v = 2

      assert(a.asInstanceOf[Cons].v == 1)
      a = a.asInstanceOf[Cons].next
      b = b.asInstanceOf[Cons].next
      i = i + 1
    }
  }
}
