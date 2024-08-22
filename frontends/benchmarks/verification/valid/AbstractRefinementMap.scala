import stainless.annotation._
import stainless.collection._
import stainless.lang._

object AbstractRefinementMap {
  def map1[A, B](l: List[A], f: A ~> B): List[B] = {
    require(l.forall(f.pre))
    l match {
      case Cons(x, xs) => Cons[B](f(x), map1(xs, f))
      case Nil() => Nil[B]()
    }
  }

  def map2[A, B](l: List[A], f: A ~>> B): List[B] = {
    require(forall((x:A) => l.contains(x) ==> f.pre(x)))
    l match {
      case Cons(x, xs) => Cons[B](f(x), map2(xs, f))
      case Nil() => Nil[B]()
    }
 }.ensuring { res => forall((x: B) => res.contains(x) ==> f.post(x)) }

  def unOpt[T](l: List[Option[T]]): List[T] = {
    require(l.forall(_.nonEmpty))
    map1(l, PartialFunction {(x:Option[T]) => require(x.nonEmpty); x.get})
  }

  def unOptCase[T](l: List[Option[T]]): List[T] = {
    require(l.forall { case Some(_) => true; case _ => false })
    map1(l, PartialFunction[Option[T], T] { case Some(v) => v })
  }
}
