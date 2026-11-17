import stainless.lang._

object OuterIdentities {
  abstract class Trees {
    case class Lit(v: BigInt)
  }
  class MyTrees(val n: BigInt) extends Trees
  case object objTrees extends Trees
  case object otherTrees extends Trees

  def mk(n: BigInt): Trees = new MyTrees(n)

  def isLitOf(t: Trees, e: Any): Boolean = e match {
    case t.Lit(_) => true
    case _ => false
  }

  // Structurally equal instances are distinct outer instances
  def distinct: Unit = {
    val a = mk(1)
    val b = mk(1)
    val l = a.Lit(0)
    assert(isLitOf(a, l))
    assert(!isLitOf(b, l))
  }

  def objects: Unit = {
    assert(isLitOf(objTrees, objTrees.Lit(1)))
    assert(!isLitOf(otherTrees, objTrees.Lit(1)))
    val t = mk(1)
    assert(!isLitOf(t, objTrees.Lit(1)))
  }

  def same(t: Trees): Unit = {
    assert(isLitOf(t, t.Lit(1)))
  }

  // Unlike type patterns, `isInstanceOf` does not test the outer instance
  def isInstance: Unit = {
    val a = mk(1)
    val b = mk(1)
    assert(a.Lit(0).isInstanceOf[b.Lit])
  }
}
