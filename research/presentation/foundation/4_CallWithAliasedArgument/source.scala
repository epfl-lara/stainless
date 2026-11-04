import stainless.lang._
object CallWriteBack {
  case class A(var x: Int)
  case class P(var l: A)

  def mutate(p: P): Unit = { p.l.x = 3 }
  def make(): A = A(0)

  def rootAlias(): Unit = {
    val p = P(A(1))
    val q = p
    mutate(p)
    assert(q.l.x == 3)
  }

  def fieldArgument(): Unit = {
    val o = P(A(1))
    val q = o
    increment(o.l)
    assert(q.l.x == 2)
  }

  def increment(a: A): Unit = { a.x = 2 }

  def freshResult(): Unit = {
    val a = make()
    val b = a
    a.x = 1
    assert(b.x == 1)
  }
}
