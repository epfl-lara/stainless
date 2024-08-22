/* Copyright 2009-2024 EPFL, Lausanne */

import stainless._
import lang._
import annotation._

object FiniteStream:

  sealed abstract class Stream:
    def rank = {
      this match
        case SCons(_, _, sz) if (sz > 0) => sz
        case _                           => BigInt(0)
    }.ensuring(_ >= 0)
  case class SCons(x: BigInt, tailFun: () => Stream, sz: BigInt) extends Stream
  case class SNil() extends Stream

  def finiteM(s: Stream): Boolean =
    decreases(s.rank)
    s match
      case SCons(_, tfun, sz) if tfun().rank >= sz =>
        false
      case SCons(_, tfun, sz) =>
        finiteM(tfun())
      case _ =>
        true


  def finite(stream: Stream): Boolean =
    decreases(stream.rank)
    stream match
      case SCons(_, tfun, sz) =>
        val tail = tfun()
        tail.rank < sz && finite(tail)
      case SNil() =>
        true
