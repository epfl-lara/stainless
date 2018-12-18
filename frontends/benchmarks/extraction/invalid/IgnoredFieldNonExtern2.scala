
import stainless.lang._
import stainless.annotation._
import scala.annotation.meta.field

object IgnoredFieldNonExtern2 {

  case class Foo(
    @(ignore @field)
    bar: scala.collection.mutable.ListBuffer[Boolean]
  )

  def test(x: Any): Unit = ()

  def wrong2(foo: Foo): Unit = {
    test(foo.bar)
  }

}
