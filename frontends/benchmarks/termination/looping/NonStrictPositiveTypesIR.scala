object NonStrictPositiveTypesIR {
  case class A(m: (A => Boolean) => Boolean)

  // f is not recursive, and does not directly refer to named functions
  def f(y: A, pp: () => A => Boolean) = y.m(pp())

  // looping only invokes f, and itself under a lambda
  // saying that looping is "terminating" is probably the issue?
  def looping(): A => Boolean = y => f(y, () => looping())

  // x1 refers to app, which is non-recursive, and to x1() itself under a lambda
  def x1(): A = A(p => app(p,x1()))

  // app is non-recursive, and does not directly refer to named functions
  def app(p: A => Boolean, x: A) = p(x)
}
