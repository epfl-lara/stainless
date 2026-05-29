package refinementMatch

import stainless.lang._
import stainless.collection._

type NonEmptyList[T] = {l: List[T] with nonEmpty(l)}

def doMatch(l: NonEmptyList[Int]): { b: Boolean with b == true } = {
  (l match {
    case l @ Cons(h, t) => true
    case Nil() => false
  }).asInstanceOf[{ b: Boolean with b == true }]
}

def nonEmpty[T](l: List[T]): Boolean =
  l match
    case Nil() => false
    case Cons(_, _) => true