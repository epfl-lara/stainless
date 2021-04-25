case class ConcreteClass() {
  def f() = 0
  def g() = {
    assert(f() == 0)
  }
}
