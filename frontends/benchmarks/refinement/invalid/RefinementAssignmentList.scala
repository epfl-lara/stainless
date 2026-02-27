sealed abstract class MyList[T]
case class Nil[T]() extends MyList[T]
case class Cons[T](head: T, tail: MyList[T]) extends MyList[T]

type NonEmptyList[T] = {l: MyList[T] with nonEmpty(l)}

val nonEmptyList: NonEmptyList[Int] = Nil[Int]().asInstanceOf[NonEmptyList[Int]]

def nonEmpty[T](l: MyList[T]): Boolean =
  l match
    case Nil() => false
    case Cons(_, _) => true