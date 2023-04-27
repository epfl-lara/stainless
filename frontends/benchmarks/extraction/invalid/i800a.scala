import stainless.annotation._

object i800a {
  case class Foo() extends Exception

  @extern
  def mystery(): Int = {
    { throw Foo() }
    3
  }

  def my(): Int = {
    try mystery() catch {
      case Foo() => 42
    }
    5
  } ensuring (_ == 5)
}