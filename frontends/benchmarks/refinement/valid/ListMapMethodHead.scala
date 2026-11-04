package listMapMethodHead

sealed abstract class MyList[T] derives CanEqual:
  def nonEmpty: Boolean
  def map[U](f: T => U): MyList[U]
  def head(using CanEqual[T, T]): T = {
    require(this != MyNil[T]())
    val MyCons(h, _) = this: @unchecked
    h
  }

case class MyNil[T]() extends MyList[T]:
  def nonEmpty: Boolean = false
  def map[U](f: T => U): MyList[U] = MyNil[U]()

case class MyCons[T](h: T, t: MyList[T]) extends MyList[T]:
  def nonEmpty: Boolean = true
  def map[U](f: T => U): MyList[U] = MyCons(f(h), t.map(f))

type NonEmptyList[T] = {l: MyList[T] with l.nonEmpty}

def mapHead[T](l: MyList[NonEmptyList[T]])(using CanEqual[T, T]) = l.map(_.head)