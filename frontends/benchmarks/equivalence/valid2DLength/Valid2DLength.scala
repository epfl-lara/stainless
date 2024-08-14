/* Copyright 2009-2024 EPFL, Lausanne */

import stainless.lang._

object Valid2DLength:

  enum Direction {
      case Left
      case Up
      case Diagonal
  }

  def valid2DLengthM(a: Array[Array[BigInt]], w: Array[Array[Direction]], m: Int, n: Int, k: Int): Boolean =
    require(a.length == m && w.length == m && a.length > 0 && w.length > 0 && k >= -1 && k < m)
    decreases(k+1)
    (k == -1) || a(k).length == n && w(k).length == n && valid2DLengthM(a, w, m, n, k - 1)


  def valid2DLength(a: Array[Array[BigInt]], w: Array[Array[Direction]], m: Int, n: Int, k: Int): Boolean =
    require(a.length == m && w.length == m && a.length > 0 && w.length > 0 && k >= -1 && k < m)
    decreases(k+1)
    if (k == -1) true
    else if (a(k).length != n) false
    else if (w(k).length != n) false
    else valid2DLength(a, w, m, n, k - 1)
