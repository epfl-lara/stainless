object TargetMutation7 {

  case class A(var i: BigInt)
  case class B(var a1: A, var a2: A)
  case class C(var a: A, var b: B)

  def createA(i: BigInt, counter: A): A = {
    counter.i += 1
    A(i)
  }

  def test1(n: BigInt, counter: A): C = {
    val origCount = counter.i
    val a0 = A(1234)
    val b = {
      if (n > 0) {
        val b = B(A(0), A(1))
        b.a1 = createA(1, counter)
        b
      } else B(A(123), A(456))
    }
    val a = createA(2, counter)
    assert(n <= 0 || counter.i == origCount + 2)
    assert(n > 0 || counter.i == origCount + 1)
    C(a, b)
  }

  def test2(n: BigInt, counter: A): Unit = {
    val origCount = counter.i
    val alias = counter
    val b = {
      if (n > 0) B(A(0), createA(n, alias))
      else B(A(0), A(0))
    }
    b.a2.i += 1
    assert(n <= 0 || counter.i == origCount + 1)
    assert(n > 0 || counter.i == origCount)
  }


  def test3(n: BigInt, counter: A): Unit = {
    val origCount = counter.i
    val alias = counter
    val b = {
      if (n > 0) {
        createA(n, alias)
        B(A(0), alias)
      }
      else B(A(0), alias)
    }
    b.a2.i += 1
    assert(n <= 0 || b.a2.i == origCount + 2)
    assert(n > 0 || b.a2.i == origCount + 1)
  }

  def test4(n: BigInt, counter: A): Unit = {
    val origCount = counter.i
    val alias = counter
    val b = {
      if (n > 0) {
        createA(n, alias)
        B(A(0), counter)
      }
      else B(A(0), alias)
    }
    b.a2.i += 1
    assert(n <= 0 || b.a2.i == origCount + 2)
    assert(n > 0 || b.a2.i == origCount + 1)
  }
}