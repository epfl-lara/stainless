import stainless.annotation._
import stainless.collection._
import stainless.lang._

object IndexOfInjective {
  @opaque
  def indexOfInjective[T](l: List[T], x1: T, x2: T): Unit = {
    require(l.contains(x1) && l.contains(x2) && x1 != x2)
    decreases(l)

    if (!l.isEmpty && l.head != x1 && l.head != x2)
      indexOfInjective(l.tail, x1, x2)

  } ensuring(_ => l.indexOf(x1) != l.indexOf(x2))
}
