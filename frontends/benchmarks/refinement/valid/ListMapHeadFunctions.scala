package listMapHeadNoMethod

sealed abstract class MyList[T]
case class Nil[T]() extends MyList[T]
case class Cons[T](head: T, tail: MyList[T]) extends MyList[T]

def nonEmpty[T](l: MyList[T]): Boolean =
  l match
    case Nil() => false
    case Cons(_, _) => true

def map[A, B](l: MyList[A], f: A => B): MyList[B] =
  l match
    case Nil() => Nil[B]()
    case Cons(h, tail) => Cons(f(h), map(tail, f))

def head[T](l: MyList[T]): T = {
  require(l != Nil[T]())
  val Cons(h, _) = l: @unchecked
  h
}

type NonEmptyList[T] = {l: MyList[T] with nonEmpty(l)}

def mapHead[T](l: MyList[NonEmptyList[T]]) = map[NonEmptyList[T], T](l, head)