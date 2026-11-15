import stainless.lang.*

object i1136:

  case class Cell[T](var value: T) extends AnyHeapRef

  def get[T](c: Cell[T]): T =
    reads(Set[AnyHeapRef](c))
    c.value

  def test[T](c: Cell[T]): T =
    reads(Set[AnyHeapRef](c))
    get(c)
