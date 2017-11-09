import stainless.lang._

sealed abstract class Foo[A] {
  val foo: Option[A]
}

case class Bar(foo: Option[Bar]) extends Foo[Bar] // <- F-Bound here

object test {

  def none = Bar(None())
  def some = Bar(Some(none))

}
