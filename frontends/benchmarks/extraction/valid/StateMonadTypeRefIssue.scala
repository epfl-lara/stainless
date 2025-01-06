object StateMonad {

  case class St[A,S](fun: S => (A,S)) {
    def ^=(that: St[A,S])(implicit anyS: S): St[A,S] = {
      assert(this.fun(anyS) == that.fun(anyS))
      that
    }

    def qed: Unit =
      ???

    def flatMap[B](f: A => St[B,S]): St[B,S] =
      St[B,S] {
        s0 =>
          val (a,s1) = fun(s0)
          f(a).fun(s1)
      }

    def unit[A,S](a: A) =
      St[A,S] {
        (s:S) => (a,s)
      }

    def leftUnit[A,S,B](a: A, f: A => St[B,S])(implicit anyS: S): Unit = {
      (unit(a).flatMap(f) ^=
      St((s:S) => (a:A,s:S)).flatMap(f) ^=
      St { (s0:S) =>
          val (a1:A,s1:S) = ((s:S) => (a,s))(s0)
          f(a1).fun(s1) } ^=
      St { s0 =>
          val (a1:A,s1:S) = (a,s0)
          f(a1).fun(s1) } ^=
      St(s0 => f(a).fun(s0)) ^=
      f(a))
      .qed
   }.ensuring(_ => unit(a).flatMap(f) == f(a))
  }
}
