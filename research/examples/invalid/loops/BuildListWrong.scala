import stainless.lang._

object BuildListWrong {
  sealed abstract class Node
  case class Cons(var v: BigInt, var next: Node) extends Node
  case class Nil() extends Node

  def f(n: BigInt): Unit = {
    var acc: Node = Nil()
    var i = BigInt(0)
    while (i < n) {
      decreases(n - i)
      val previous = acc
      acc = Cons(i, acc)
      if (previous.isInstanceOf[Cons]) {
        previous.asInstanceOf[Cons].v = 50

        assert(acc.asInstanceOf[Cons].next.asInstanceOf[Cons].v == 49)
      }
      i = i + 1
    }
  }
}
