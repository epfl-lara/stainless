/* Example based on discussion with Pierre Quinton */

import stainless.lang._
import stainless.annotation._

abstract class A[T] {
  def a: T
  def f(x: T, y: T): T

  @law
  def uniqueRight(x: T, y: T, z: T): Boolean = {
    f(x,y) != f(x,z) || y == z
  }
}

object Aux {
  def something[T](ceci: A[T], x: T, y: T): Boolean = {
    require(ceci.f(x,y) == ceci.f(x,ceci.a))
    ceci.uniqueRight(x,y,ceci.a)
    y == ceci.a
  }.holds

  def somethingelse[T](ceci: A[T], y: T): Unit = {
    require(ceci.f(ceci.a,ceci.a) == ceci.f(ceci.a,y))
    assert(something(ceci, ceci.a,y))
  }.ensuring(y == ceci.a)  
}
