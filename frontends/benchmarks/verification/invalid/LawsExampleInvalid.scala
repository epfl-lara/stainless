/* Example based on discussion with Pierre Quinton. 
   This fails, as it should. See ../valid/LawsExample.scala for working version. */

import stainless.lang._
import stainless.annotation._

abstract class A[T] {
  def a: T
  def f(x: T, y: T): T

  @law
  def uniqueRight(x: T, y: T, z: T): Boolean = {
    f(x,y) != f(x,z) || y == z
  }

  def something(x: T, y: T): Boolean = {
    require(f(x,y) == f(x,a))
    uniqueRight(x,y,a)
    y == this.a
  }.holds

  def somethingelse(y: T): Unit = {
    require(f(a,a) == f(a,y))
    assert(something(a,y))
  }.ensuring(y == a)  
}

