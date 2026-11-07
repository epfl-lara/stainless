import stainless.lang._

object NestedTraversal {
  sealed abstract class Node
  case class Cons(var v: BigInt, var next: Node) extends Node
  case class Nil() extends Node

  def make(): Node = Cons(0, Cons(1, Cons(2, Nil())))

  def f(n: BigInt, m: BigInt): Unit = {
    require(n >= 0 && m >= 0)

    var j = BigInt(0)
    while (j < m) {
      decreases(m - j)
      var cur: Node = make()
      var i = BigInt(0)
      while (i < n && cur.isInstanceOf[Cons]) {
        decreases(n - i)
        val c = cur.asInstanceOf[Cons]

        c.v = j

        assert(c.v == j)
        cur = c.next
        i = i + 1
      }
      j = j + 1
    }
  }
}
