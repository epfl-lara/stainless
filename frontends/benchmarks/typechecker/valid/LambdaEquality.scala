/* Copyright 2009-2018 EPFL, Lausanne */


import stainless.lang._
import stainless.annotation._
import stainless.collection._

object LambdaEquality {
  def app[A, B](x: A)(f: A => B): B = f(x)

  // TYPEFIX: @induct

  // @induct
  // def mapId[A](xs: List[A]): Boolean = {
  //   xs.map[A](id) == xs && {
  //     xs match {
  //       case Nil() => true
  //       case Cons(x, xs) =>
  //         mapId(xs) &&
  //         id(x) :: xs.map[A](id) == x :: xs &&
  //         true
  //     }
  //   }
  // }.holds

  def id[A](a: A): A = a

  def mapEquality1[A, B](xs: List[A])(f: A => B): Boolean = {
    xs.map(f) == xs.map(f)
  }.holds

  def mapEquality2[A, B](xs: List[A])(f: A => B): Boolean = {
    xs.map(id) == xs.map(id)
  }.holds

}
