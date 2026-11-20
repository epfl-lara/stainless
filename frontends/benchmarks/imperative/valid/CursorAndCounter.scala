import stainless.lang._

object CursorAndCounter {
  sealed abstract class Node
  case class Cons(var v: BigInt, var next: Node) extends Node
  case class Nil() extends Node

  case class Box(var value: BigInt)

  def make(): Node = Cons(0, Cons(1, Cons(2, Nil())))

  def f(n: BigInt): Unit = {
    val counter = Box(0)
    var cur: Node = make()
    var i = BigInt(0)
    while (i < n && cur.isInstanceOf[Cons]) {
      decreases(n - i)

      counter.value = counter.value + cur.asInstanceOf[Cons].v
      cur.asInstanceOf[Cons].v = 0

      cur = cur.asInstanceOf[Cons].next
      i = i + 1
    }

    assert(counter.value >= 0 || counter.value < 0)
  }
}
