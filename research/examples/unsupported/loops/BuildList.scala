import stainless.lang._

object BuildList {
  sealed abstract class Node
  case class Cons(var v: BigInt, var next: Node) extends Node
  case class Nil() extends Node

  def f(n: BigInt): Unit = {
    var acc: Node = Nil()
    var i = BigInt(0)
    while (i < n) {
      decreases(n - i)
      acc = Cons(i, acc)

      acc.asInstanceOf[Cons].v = acc.asInstanceOf[Cons].v + 1

      assert(acc.asInstanceOf[Cons].v == i + 1)
      i = i + 1
    }
  }
}
