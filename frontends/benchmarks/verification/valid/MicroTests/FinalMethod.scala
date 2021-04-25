trait FinalMethod {
  final def f() = 0

  def g() = {
    assert(f() == 0)
  }
}
