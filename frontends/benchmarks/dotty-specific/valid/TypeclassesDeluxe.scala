import stainless.lang._
import stainless.collection._
import stainless.annotation._

// See https://docs.scala-lang.org/scala3/reference/contextual/type-classes.html
object TypeclassesDeluxe {
  trait SemiGroup[T] {
    extension (x: T) def combine(y: T): T

    @law
    def law_associativity(x: T, y: T, z: T) =
      x.combine(y.combine(z)) == x.combine(y).combine(z)
  }

  trait Monoid[T] extends SemiGroup[T] {
    def unit: T

    @law
    def law_leftIdentity(x: T) =
      unit.combine(x) == x

    @law
    def law_rightIdentity(x: T) =
      x.combine(unit) == x
  }

  case object MonoidString extends Monoid[String]:
    extension (x: String) def combine (y: String): String = x + y
    def unit: String = ""

  // Explicit given because we don't support fancy object definitions anymore  
  given stringMonoid: Monoid[String] = MonoidString

  def fold[T](l: List[T])(using m: Monoid[T]) =
    l.foldLeft(m.unit)(_.combine(_))


  def test: Boolean = {
    fold(Cons("Hello", Cons(" World!", Nil()))) == "Hello World!"
  }.holds
}