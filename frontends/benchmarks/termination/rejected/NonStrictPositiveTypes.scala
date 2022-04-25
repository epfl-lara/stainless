object NonStrictPositiveTypes {
  case class A(m: (A => Boolean) => Boolean)

  def looping(): A => Boolean = y => y.m(looping())
  def x(): A = A(p => p(x()))

  // looping()(x()) reduces to x().m(looping()) and
  // x().m(looping()) reduces to looping()(x()) (does not terminate)
}
