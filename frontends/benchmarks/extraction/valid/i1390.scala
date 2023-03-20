import stainless.lang._
import stainless.collection._

object i1390 {
  object Types {
    type I = Int
  }

  import Types._

  case class Foo(bar: Map[I, String])
}