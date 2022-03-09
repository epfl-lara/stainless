object i1051i {
  case class A(val b: B, val container: Container)
  case class Container(arr: Array[B], var other: Int)
  case class B(var c1: C, var c2: C, var d: D)
  case class C(var x: Int)
  case class D(var c: C)

  def t1(a: A, i: Int): Unit = {
    require(0 <= i && i < a.container.arr.length)
    a.container.arr(i) = B(C(1), C(2), D(C(3)))
    assert(a.container.arr(i).d.c.x == 3)
  }

  def t2(a: A, i: Int): Unit = {
    require(0 <= i && i < a.container.arr.length)
    a.container.arr(i).c1 = C(123)
    assert(a.container.arr(i).c1.x == 123)
  }
}