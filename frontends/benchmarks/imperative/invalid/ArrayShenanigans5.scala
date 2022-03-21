import stainless.lang._
import stainless.annotation._

object ArrayShenanigans5 {
  case class A(val b: B, val container: Container)
  case class Container(arr: Array[B], var other: Int)
  case class B(var c1: C, var c2: C, var d: D)
  case class C(var x: Int)
  case class D(var c: C)

  def test(a: A, i: Int, j: Int, cond: Boolean): Unit = {
    require(0 <= i && i < a.container.arr.length)
    require(0 <= j && j < a.container.arr.length)

    val oldIC1 = a.container.arr(i).c1.x
    val arrij = if (cond) a.container.arr(i) else a.container.arr(j)
    arrij.c1.x = 42
    assert(a.container.arr(i).c1.x == oldIC1)
  }
}
