
import stainless.lang._
import stainless.annotation._

object Rewriter {

  sealed abstract class List[A]

  case class Nil[A]() extends List[A]
  case class Cons[A](head: A, tail: List[A]) extends List[A]

  def append[A](xs: List[A], x: A): List[A] = xs match {
    case Nil() => Cons(x, Nil())
    case Cons(y, ys) => Cons(y, append(ys, x))
  }

  def reverse[A](list: List[A]): List[A] = list match {
    case Nil() => Nil()
    case Cons(x, xs) => append(reverse(xs), x)
  }

  def concat[B](l: List[B], r: List[B]): List[B] = l match {
    case Nil() => r
    case Cons(x, xs) => Cons(x, concat(xs, r))
  }

  @rewriteRule
  def rewrite_revRev[A](list: List[A]) = {
    require(list != Nil[A]())
    reverse(reverse(list)) == list
  }

  @rewriteRule
  def rewrite_reverseAppend[B](l1: List[B], l2: List[B]) = {
    reverse(concat(l1, l2)) == concat(reverse(l2), reverse(l1))
  }

  @rewrite
  def test[T](a: T, ls: List[T]) = {
    val res = reverse(reverse(Cons(a, Cons(a, ls))))
    assert(rewrite_revRev(Nil[T]()))
    assert(rewrite_reverseAppend(Nil[T](), Nil[T]()))
    reverse(concat(res, res))
  }

}
