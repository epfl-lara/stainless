import stainless.lang._

object FloatTypeParams {
  trait One {
    type T
    def f(): Option[T]
  }

  case object OneImplFloat extends One {
    type T = Float
    def f(): Option[T] = None()
  }

  case object OneImplDouble extends One {
    type T = Double
    def f(): Option[T] = None()
  }

  abstract class Test[A] {
    def something: A
  }

  case class FooBar[B, C](b: B, c: C) extends Test[B] {
    def something: B = b
  }

  def test = {
    FooBar(3.14f, 2.72d).something == 3.14f && FooBar(2.72d, 3.14f).something == 2.72d
  }.holds
}