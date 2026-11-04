import stainless.lang._
object CallSharedArgumentTrees {
  case class A(var x: Int)
  case class P(var l: A)

  def bump(p: P, q: P): Unit = {
    p.l.x = 1
    q.l.x = 2
    assert(p.l.x == 1) // proved assuming p and q share nothing
  }

  def sharedTrees(): Unit = {
    val a = A(0)
    val p = P(a)
    val q = P(a)       // the heap just before the call in caller
  }

  def caller(): Unit = {
    val a = A(0)
    val p = P(a)
    val q = P(a)       // p.l and q.l are the same object
    bump(p, q)         // at runtime p.l.x == 2: the callee's assertion would be false
  }
}
