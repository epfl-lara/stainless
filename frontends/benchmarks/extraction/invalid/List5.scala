//no import of stainless.collection.List

object List5 {
  type MyList[T] = List[T]
  def foobar[T](l: MyList[T]) = {
    require(l.size > 0)
    l.head
  }
}
