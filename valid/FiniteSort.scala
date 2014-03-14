/* Copyright 2009-2014 EPFL, Lausanne */

import leon.lang._

object FiniteSorting {

  // These finite sorting functions essentially implement insertion sort.
  def sort2(x : Int, y : Int) : (Int,Int) = {
    if(x < y) (x, y) else (y, x)
  } ensuring (_ match {
    case (a, b) => a <= b && Set(a,b) == Set(x,y)
  })

  def sort3(x1 : Int, x2 : Int, x3 : Int) : (Int, Int, Int) = {
    val (x1s, x2s) = sort2(x1, x2)

    if(x2s <= x3) {
      (x1s, x2s, x3)
    } else if(x1s <= x3) {
      (x1s, x3, x2s)
    } else {
      (x3, x1s, x2s)
    }
  } ensuring (_ match {
    case (a, b, c) => a <= b && b <= c && Set(a,b,c) == Set(x1,x2,x3)
  })

  def sort4(x1 : Int, x2 : Int, x3 : Int, x4 : Int) : (Int, Int, Int, Int) = {
    val (x1s, x2s, x3s) = sort3(x1, x2, x3)

    if(x3s <= x4) {
      (x1s, x2s, x3s, x4)
    } else if(x2s <= x4) {
      (x1s, x2s, x4, x3s)
    } else if(x1s <= x4) {
      (x1s, x4, x2s, x3s)
    } else {
      (x4, x1s, x2s, x3s)
    }
  } ensuring (_ match {
    case (a, b, c, d) => a <= b && b <= c && c <= d && Set(a,b,c,d) == Set(x1,x2,x3,x4)
  })

  def sort5(x1 : Int, x2 : Int, x3 : Int, x4 : Int, x5 : Int) : (Int, Int, Int, Int, Int) = {
    val (x1s, x2s, x3s, x4s) = sort4(x1, x2, x3, x4)

    if(x4s <= x5) {
      (x1s, x2s, x3s, x4s, x5)
    } else if(x3s <= x5) {
      (x1s, x2s, x3s, x5, x4s)
    } else if(x2s <= x5) {
      (x1s, x2s, x5, x3s, x4s)
    } else if(x1s <= x5) {
      (x1s, x5, x2s, x3s, x4s)
    } else {
      (x5, x1s, x2s, x3s, x4s)
    }
  } ensuring (_ match {
    case (a, b, c, d, e) => a <= b && b <= c && c <= d && d <= e && Set(a,b,c,d,e) == Set(x1,x2,x3,x4,x5)
  })
}
