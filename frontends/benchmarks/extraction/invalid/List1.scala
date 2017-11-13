//no import of stainless.collection.List

object List1 {
  def foobar[T](l: List[T]) = {
    require(l.size > 0)
    l.head
  }
}
