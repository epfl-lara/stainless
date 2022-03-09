object i1051a {
  case class A(val left: B, val right: B)
  case class B(var c: C, var d: D)
  case class C(var x: Int)
  case class D(var y: Int)

  def t1(a: A): Unit = {
    // This line gets transformed (by AntiAliasing) to:
    // val res: (Unit, A) = g(a)
    // a = A(B(C(res._2.left.c.x, a.left.d)), a.right)
    // The set of targets for the arguments passed to A are:
    //   B(C(res._2.left.c.x, a.left.d)):
    //     a with path .left.d
    //     (res._2.left.c.x is not a target because its type, Int, is immutable)
    //   a.right:
    //     a with path .right
    // The targets are disjoint so there no illegal aliasing (as we would expect)
    g(a)
    assert(a.left.c.x == 123)
  }

  def g(a: A): Unit = {
    // This line gets transformed (by AntiAliasing) to:
    //   a = A(B(C(123), a.left.d), a.right)
    // The set of targets for the arguments passed to A are:
    //   B(C(123), a.left.d):
    //     a with path .left.d
    //   a.right:
    //     a with path .right
    // The targets are disjoint so there no illegal aliasing (as we would expect)
    a.left.c.x = 123
  }
}