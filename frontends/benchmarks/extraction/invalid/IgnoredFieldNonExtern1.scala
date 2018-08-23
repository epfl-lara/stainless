
import stainless.lang._
import stainless.annotation._
import scala.annotation.meta.field

object IgnoredField {

  case class Foo(
    @(ignore @field)
    bar: Option[Boolean]
  )

  def wrong1 = {
    Foo(Some(true))
  }

}
