import stainless.lang._

object OuterIdentities {
  abstract class Trees {
    case class Lit(v: BigInt)
  }
  class MyTrees(val n: BigInt) extends Trees

  def mk(n: BigInt): Trees = new MyTrees(n)

  def isLitOf(t: Trees, e: Any): Boolean = e match {
    case t.Lit(_) => true
    case _ => false
  }

  // Scala compares outer instances by reference
  def structural: Unit = {
    val a = mk(1)
    val b = mk(1)
    assert(isLitOf(a, b.Lit(0)))
  }

  // The instances may be the same
  def unknown(t1: Trees, t2: Trees): Unit = {
    assert(!isLitOf(t2, t1.Lit(0)))
  }
}
