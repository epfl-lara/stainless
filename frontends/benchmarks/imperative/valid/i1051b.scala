object i1051b {
  case class A(val left: B, val right: B)
  case class B(var c1: C, var c2: C)
  case class C(var x: Int)

  def t1(a: A): Unit = {
    // This line gets transformed (by AntiAliasing) to:
    // val res: (Unit, A) = g(a)
    // a = A(B(res._2.left.c1, a.left.c2), a.right)
    // The set of targets for the arguments passed to A are:
    //   B(res._2.left.c1, a.left.c2):
    //     res with path _2.left.c1
    //     a   with path .left.c2
    //   a.right:
    //     a with path .right
    // The targets are pairwise disjoint so there no illegal aliasing (as we would expect)
    g(a)
    assert(a.left.c1.x == 123)
  }

  def g(a: A): Unit = {
    // This line gets transformed (by AntiAliasing) to:
    //   a = A(B(C(123), a.left.c2), a.right)
    // The set of targets for the arguments passed to A are:
    //   B(C(123), a.left.c2):
    //     a with path .left.c2
    //   a.right:
    //     a with path .right
    // The targets are disjoint so there no illegal aliasing (as we would expect)
    a.left.c1 = C(123)
  }
}