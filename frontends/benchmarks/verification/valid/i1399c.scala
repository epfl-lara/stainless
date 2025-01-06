import stainless.lang._
import stainless.collection._
import stainless.annotation._

object i1399c {

  case class L(a: A)
  case class A(m: M)
  case class M(b: B)
  case class B(d: D)
  case class D(a: AA)
  case class AA(x: BigInt)

  def foo(key: Boolean): Boolean = false

  def bar1(l: List[L]): List[(AA, D)] = l.map { l =>
    val m = l.a.m
    (m.b.d.a, m.b.d)
  }

  def bar2(l: List[L]): List[(AA, D)] = l.map(l => (l.a.m.b.d.a, l.a.m.b.d))


  def bar1EqualsItsBody(l: List[L]): Unit = {
 }.ensuring(bar1(l) == l.map { l =>
    val m = l.a.m
    (m.b.d.a, m.b.d)
  })

  def bar1EqualsBar2Body(l: List[L]): Unit = {
 }.ensuring(bar1(l) == l.map(l => (l.a.m.b.d.a, l.a.m.b.d)))


  def bar2EqualsItsBody1(l: List[L]): Unit = {
 }.ensuring(bar2(l) == l.map(l => (l.a.m.b.d.a, l.a.m.b.d)))

  def bar2EqualsBar1Body(l: List[L]): Unit = {
 }.ensuring(bar2(l) == l.map { l =>
    val m = l.a.m
    (m.b.d.a, m.b.d)
  })

  def bar1EqualsBar2(l: List[L]): Unit = {
 }.ensuring(bar1(l) == bar2(l))
}
