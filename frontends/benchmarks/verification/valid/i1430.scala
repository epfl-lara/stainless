import stainless.covcollection._

object i1430 {
  case class Set[T]() {
    def funTrue: T => Boolean = t => true
  }

  def foo[T](l: List[T]): Set[T] = Set[T]()

  def bug[T](l: List[T], n: T): Unit = {
    require(foo[T](l).funTrue(n))
  }
}
