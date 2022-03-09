import stainless.annotation._

object i1051b {
  sealed abstract class List[@mutable T]
  case class Nil[@mutable T]() extends List[T]
  case class Cons[@mutable T](var head: T, var tail: List[T]) extends List[T]
  final case class C(var x:Int)

  @pure
  def make(c: C): List[C] =
    Cons(c, Cons(c, Nil[C]())) // Illegal passing of aliased parameters
}