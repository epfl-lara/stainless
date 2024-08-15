/* Copyright 2009-2024 EPFL, Lausanne */

import stainless.lang._
import stainless.collection._

object AdjList:

  def validAdjListM(adjList: Array[List[Int]], N: Int, pos: Int): Boolean =
    require(N >= 1 && pos >= 0 && pos <= N && N == adjList.length)
    decreases(pos)
    if pos == 0 then
      true
    else
      validListM(adjList(pos - 1), N) && validAdjListM(adjList, N, pos - 1)

  def validListM(list: List[Int], N: Int): Boolean =
    require(N >= 1)
    list match
      case Nil() =>
        true
      case Cons(h, t) =>
        h >= 0 && h < N && validListM(t, N)


  def validAdjList(adjList: Array[List[Int]], N: Int, pos: Int): Boolean =
    require(N >= 1 && pos >= 0 && pos <= N && N == adjList.length)
    decreases(pos)
    if (pos == 0) then
      true
    else if (validAdjList(adjList, N, pos - 1)) then
      validList(N, adjList(pos - 1))
    else
      false

  def validList(N: Int, l: List[Int]): Boolean =
    require(N >= 1)
    l match
      case Cons(h, t) if (h >= 0 && h < N) =>
        validList(N, t)
      case _ =>
        l.size == 0
