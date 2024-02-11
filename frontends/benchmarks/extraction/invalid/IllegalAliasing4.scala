object IllegalAliasing4 {

  case class A(var i: BigInt)
  case class B(a: A)
  case class C(a: A, b: B)

  def createA(i: BigInt, counter: A): A = {
    counter.i += 1
    A(i)
  }

  def test(n: BigInt, counter: A): Unit = {
    val origCount = counter.i
    val alias = counter
    val b = {
      if (n > 0) {
        createA(n, alias)
        B(alias)
      }
      else B(A(0))
    }
    b.a.i += 1
    assert(n <= 0 || counter.i == origCount + 2)
    assert(n > 0 || counter.i == origCount + 1)
  }
}