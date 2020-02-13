/* Copyright 2009-2019 EPFL, Lausanne */

import stainless._
import lang._
import annotation._
import collection._
import math._

object LazyVal {

  sealed abstract class Stream[T] {
    def isEmpty: Boolean = this == SNil[T]()
    def isCons: Boolean = !isEmpty

    lazy val stail: Stream[T] = {
      require(isCons)
      this match {
        case SCons(_, tfun, _) => tfun()
      }
    }
  }

  private case class SCons[T](x: T, tfun: () => Stream[T], sz: BigInt) extends Stream[T]
  private case class SNil[T]() extends Stream[T]

  def force[T](tar: Stream[T]): Stream[T] = {
    tar match {
      case c @ SCons(_, _,_) => c.stail
      case _               => tar
    }
  }
}
