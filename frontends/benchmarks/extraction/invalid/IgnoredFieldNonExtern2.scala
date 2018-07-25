
import stainless.lang._
import stainless.annotation._
import scala.annotation.meta.field

object IgnoredField {

  case class Foo(
    @(ignore @field)
    bar: Option[Boolean]
  )

  def wrong2(foo: Foo) = {
    foo.bar.isDefined
  }

}
