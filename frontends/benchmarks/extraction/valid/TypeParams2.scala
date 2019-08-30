import stainless.lang._

object TypeParams2 {
  abstract class Test[A] {
    def something: A
  }

  case class FooBar[B, C](b: B, c: C) extends Test[B] {
    def something: B = b
  }

  def test = {
    FooBar(true, 42).something == true
  }.holds
}
