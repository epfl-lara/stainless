import stainless.lang._

object ADTInvariants4 {

  // TYPEFIX: ADT invariant

  // abstract class Foo {
  //   def bar: Option[Bar]
  // }

  // case class Bar(bar: Option[Bar]) extends Foo {
  //   require(bar.isDefined)
  // }

  // def test(foo: Foo): Boolean = (foo match {
  //   case Bar(b) => b.nonEmpty
  //   case _ => true
  // }).holds
}
