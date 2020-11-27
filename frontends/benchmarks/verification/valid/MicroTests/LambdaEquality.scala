/* Copyright 2009-2019 EPFL, Lausanne */


import stainless.lang._
import stainless.annotation._
import stainless.collection._

object LambdaEquality {
  def app[A, B](x: A)(f: A => B): B = f(x)

  def mapId[A](@induct xs: List[A]): Boolean = {
    xs.map[A](id) == xs
  }.holds

  def id[A](a: A): A = a

  def mapEquality1[A, B](xs: List[A])(f: A => B): Boolean = {
    xs.map(f) == xs.map(f)
  }.holds

  def mapEquality2[A, B](xs: List[A])(f: A => B): Boolean = {
    xs.map(id) == xs.map(id)
  }.holds

}
