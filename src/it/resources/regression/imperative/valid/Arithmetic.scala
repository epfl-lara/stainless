/* Copyright 2009-2016 EPFL, Lausanne */

import stainless.lang._

object Arithmetic {

  /* VSTTE 2008 - Dafny paper */
  def mult(x : BigInt, y : BigInt): BigInt = ({
    var r: BigInt = 0
    if(y < 0) {
      var n = y
      (while(n != BigInt(0)) {
        r = r - x
        n = n + 1
      }) invariant(r == x * (y - n) && 0 <= -n)
    } else {
      var n = y
      (while(n != BigInt(0)) {
        r = r + x
        n = n - 1
      }) invariant(r == x * (y - n) && 0 <= n)
    }
    r
  }) ensuring(_ == x*y)

  /* VSTTE 2008 - Dafny paper */
  def add(x : BigInt, y : BigInt): BigInt = ({
    var r = x
    if(y < 0) {
      var n = y
      (while(n != BigInt(0)) {
        r = r - 1
        n = n + 1
      }) invariant(r == x + y - n && 0 <= -n)
    } else {
      var n = y
      (while(n != BigInt(0)) {
        r = r + 1
        n = n - 1
      }) invariant(r == x + y - n && 0 <= n)
    }
    r
  }) ensuring(_ == x+y)


  def sum(n: BigInt): BigInt = {
    require(n >= 0)
    var r = BigInt(0)
    var i = BigInt(0)
    (while(i < n) {
      i = i + 1
      r = r + i
    }) invariant(r >= i && i >= 0 && r >= 0)
    r
  } ensuring(_ >= n)

  def divide(x: BigInt, y: BigInt): (BigInt, BigInt) = {
    require(x >= 0 && y > 0)
    var r = x
    var q = BigInt(0)
    (while(r >= y) {
      r = r - y
      q = q + 1
    }) invariant(x == y*q + r && r >= 0)
    (q, r)
  } ensuring(res => x == y*res._1 + res._2 && res._2 >= 0 && res._2 < y)

}
