import stainless.lang._
import stainless.annotation._
import scala.collection.immutable.{Set => ScalaSet}

object i1401b {
  // No, must annotate the field with @extern
  case class Set[T](s: ScalaSet[T])
}