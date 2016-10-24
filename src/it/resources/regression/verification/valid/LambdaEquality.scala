/* Copyright 2009-2016 EPFL, Lausanne */

 
import leon.lang._
import leon.annotation._
import leon.collection._
 
object LambdaEquality {
  def app[A, B](x: A)(f: A => B): B = f(x)

  @induct
  def mapId[A](xs: List[A]): Boolean = {
    xs.map(id) == xs && {
      xs match {
        case Nil() => true
        case Cons(x, xs) =>
          mapId(xs) &&
          id(x) :: xs.map(id) == x :: xs &&
          true
      }
    }
  }.holds

  def id[A](a: A): A = a

  def mapEquality1[A, B](xs: List[A])(f: A => B): Boolean = {
    xs.map(f) == xs.map(f)
  }.holds

  def mapEquality2[A, B](xs: List[A])(f: A => B): Boolean = {
    xs.map(id) == xs.map(id)
  }.holds

}
