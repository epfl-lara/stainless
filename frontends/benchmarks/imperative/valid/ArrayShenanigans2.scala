object ArrayShenanigans2 {
  case class A(val b: B, val container: Container)
  case class Container(arr: Array[B], var other: Int)
  case class B(var c1: C, var c2: C, var d: D)
  case class C(var x: Int)
  case class D(var c: C)

  def t1(a: A, i: Int): Unit = {
    require(0 <= i && i < a.container.arr.length)
    g(a.container.arr(i))
    assert(a.container.arr(i).c1.x == 123)
  }

  def g(b: B): Unit = {
    b.c1 = C(123)
  }
}