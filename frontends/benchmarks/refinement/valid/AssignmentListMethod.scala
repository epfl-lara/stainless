package assignmentListMethod

sealed abstract class MyList[T]:
  def nonEmpty: Boolean

case class Nil[T]() extends MyList[T]:
  def nonEmpty: Boolean = false

case class Cons[T](head: T, tail: MyList[T]) extends MyList[T]:
  def nonEmpty: Boolean = true

type NonEmptyList[T] = {l: MyList[T] with l.nonEmpty}

val nonEmptyList: NonEmptyList[Int] = Cons(1, Nil()).asInstanceOf[NonEmptyList[Int]]