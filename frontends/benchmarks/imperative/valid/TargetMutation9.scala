object TargetMutation9 {

  case class A(var x: BigInt)
  case class C(a: A)
  case class D(c: C)

  def test1(n: BigInt): Unit = {
    val a = A(n)
    val c = C(a)
    c.a.x = 3
    assert(c.a.x == 3)
  }

  def test2(n: BigInt): Unit = {
    val a = A(n)
    if (n == 0) {
      val c = C(a)
      c.a.x = 3
      // `a` will be updated here by AntiAliasing (`copyEffects`)
    }
    assert(n != 0 || a.x == 3)
  }

  def test3(n: BigInt): Unit = {
    val a = A(n)
    if (n == 0) {
      val c = C(a)
      val c2 = c
      c2.a.x = 3
      // `a` will be updated here by AntiAliasing (`copyEffects`)
    }
    assert(n != 0 || a.x == 3)
  }

  def test4(n: BigInt): Unit = {
    val a = A(n)
    if (n == 0) {
      val c = C(a)
      val d = D(c)
      d.c.a.x = 3
      // `a` will be updated here by AntiAliasing (`copyEffects`)
    }
    assert(n != 0 || a.x == 3)
  }

  def test5(n: BigInt): Unit = {
    val a = A(n)
    if (n == 0) {
      val c = C(a)
      val d = D(c)
      d.c.a.x = 3
      // `a` will be updated here by AntiAliasing (`copyEffects`)
    }
    a.x += 1
    assert(n != 0 || a.x == 4)
    assert(n == 0 || a.x == n + 1)
  }
}