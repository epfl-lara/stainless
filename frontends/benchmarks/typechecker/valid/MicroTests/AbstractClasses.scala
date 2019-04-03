object AbstractClasses {
  abstract class A

  case class Wrapper(a: A) {
    def g() = f(a)
  }

  def f(a: A) = true
}
