/* Copyright 2009-2019 EPFL, Lausanne */

import stainless._
import lang._
import annotation._
import collection._

/**
 * Termination can be proved without any ranking functions
 */
object RealTimeQueue {

  sealed abstract class Stream[T] {
    def isEmpty: Boolean = this == SNil[T]()
    def isCons: Boolean = !isEmpty

    lazy val tail: Stream[T] = {
      require(isCons)
      this match {
        case SCons(x, tailFun) => tailFun()
      }
    }
  }
  private case class SCons[T](x: T, tailFun: () => Stream[T]) extends Stream[T]
  private case class SNil[T]() extends Stream[T]

  def rotate[T](f: Stream[T], r: List[T], a: Stream[T]): Stream[T] = {
    decreases(r)
    (f, r) match {
      case (SNil(), Cons(y, _)) =>
        SCons[T](y, () => a)
      case (c@SCons(x, _), Cons(y, r1)) =>
        val newa = SCons[T](y, () => a)
        val ftail = c.tail
        val rot = () => rotate(ftail, r1, newa)
        SCons[T](x, rot)
      case _ => SNil()
    }
  }

  case class Queue[T](f: Stream[T], r: List[T], s: Stream[T]) {
    def isEmpty = f.isEmpty
  }

  def createQ[T](f: Stream[T], r: List[T], s: Stream[T]) = {
    s match {
      case c@SCons(_, _) => Queue(f, r, c.tail) // force the schedule once
      case SNil() =>
        val rotres = rotate(f, r, SNil[T]())
        Queue(rotres, Nil(), rotres)
    }
  }

  def empty[T] = {
    val a: Stream[T] = SNil()
    Queue(a, Nil(), a)
  }

  def head[T](q: Queue[T]): T = {
    require(!q.isEmpty)
    q.f match {
      case SCons(x, _) => x
    }
  }

  def enqueue[T](x: T, q: Queue[T]): Queue[T] = {
    createQ(q.f, Cons(x, q.r), q.s)
  }

  def dequeue[T](q: Queue[T]): Queue[T] = {
    require(!q.isEmpty)
    q.f match {
      case c@SCons(x, _) =>
        createQ(c.tail, q.r, q.s)
    }
  }
}
