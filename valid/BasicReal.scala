/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._
import leon.annotation._

object BasicReal {

  def plusOfPositiveNumbers(x: Real, y: Real): Real = {
    require(x >= Real(0) && y >= Real(0))
    x + y
  } ensuring(_ >= Real(0))


  def max(x: Real, y: Real): Real = {
    if(x >= y) x else y
  } ensuring(res => (res == x || res == y) && res >= x && res >= y)


  def divBy2(x: Real): Boolean = {
    x/Real(2) == x*Real(1,2)
  }.holds

  def twice(x: Real): Real = {
    require(x > Real(0))
    Real(2)*x
  } ensuring(res => res > x)

}
