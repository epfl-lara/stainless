/* Copyright 2009-2024 EPFL, Lausanne */

import stainless.lang._

object ArrayIncreasing:

  def validLengthIncreasingM(a:Array[Array[Int]], N:Int, M:Int, k: Int): Boolean =
    require(N > 0 && N == a.length && M > 0 && k >= 0 && k <= N)
    decreases(N - k)
    if (k == N) then
      true
    else
      a(k).length == M && validLengthIncreasingM(a, N, M, succM(k))

  def succM(n: Int) =
    require(n < Int.MaxValue)
    n + 1


  def validLengthIncreasing(a:Array[Array[Int]], N:Int, M:Int, k: Int): Boolean =
    require(N > 0 && N == a.length && M > 0 && k >= 0 && k <= N)
    decreases(N - k)
    (k == N) || a(k).length == M && validLengthIncreasing(a, N, M, k + 1)
