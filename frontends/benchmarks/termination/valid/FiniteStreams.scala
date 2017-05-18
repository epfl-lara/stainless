/* Copyright 2009-2016 EPFL, Lausanne */

import stainless._
import lang._
import annotation._

object FiniteStream {

  sealed abstract class Stream {
    def rank = this match {
      case SCons(_, _, sz) if (sz > 0) => sz
      case _                           => BigInt(0)
    }
  }
  private case class SCons(x: BigInt, tailFun: () => Stream, sz: BigInt) extends Stream
  private case class SNil() extends Stream

  def finite(s: Stream): Boolean = {
    decreases(s.rank)
    s match {
      case SCons(_, tfun, sz) =>
        val tail = tfun()
        tail.rank >= 0 && (tail.rank < sz) && finite(tail)
      case SNil() => true
    }
  }

  def filter(p: BigInt => Boolean, s: Stream): Stream = {
    require(finite(s))
    decreases(s.rank)
    s match {
      case SCons(y, tfun, _) =>
        val tail = tfun()
        if(p(y))
          SCons(y, () => filter(p, tail), s.rank)
        else
          filter(p, tail)
      case SNil() =>
        SNil()
    }
  } ensuring (res => finite(res) && res.rank <= s.rank)
}
