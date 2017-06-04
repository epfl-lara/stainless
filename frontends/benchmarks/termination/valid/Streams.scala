/* Copyright 2009-2016 EPFL, Lausanne */

import stainless.lang._

object Streams {

  sealed abstract class Stream[T] {
    def map[U](f: T => U): Stream[U] = this match {
      case SCons(x, tfun) => SCons(f(x), () => tfun().map(f))
      case SNil() => SNil()
    }

    def ++(that: Stream[T]): Stream[T] = this match {
      case SCons(x, tfun) => SCons(x, () => tfun() ++ that)
      case SNil() => that
    }

    def drop(i: BigInt): Stream[T] = {
      require(i >= 0)
      this match {
        case SCons(x, tfun) if i > 0 => tfun().drop(i - 1)
        case _ => this
      }
    }

    def take(i: BigInt): Stream[T] = {
      require(i >= 0)
      this match {
        case SCons(x, tfun) if i > 0 => SCons(x, () => tfun().take(i - 1))
        case _ => SNil()
      }
    }

    def zip[U](that: Stream[U]): Stream[(T, U)] = (this, that) match {
      case (SCons(x, xs), SCons(y, ys)) => SCons((x, y), () => xs() zip ys())
      case _ => SNil()
    }

    def scanLeft[U](z: U)(f: (U,T) => U): Stream[U] = SCons(z, () => this match {
      case SCons(x, tfun) => tfun().scanLeft(f(z, x))(f)
      case SNil() => SNil()
    })

    /* ---- non terminating ----
     *
     * def flatMap[U](f: T => Stream[U]): Stream[U] = this match {
     *   case SCons(x, tfun) => f(x) ++ (tfun() flatMap f)
     *   case SNil() => SNil()
     * }
     *
     * def filter(p: T => Boolean): Stream[T] = this match {
     *   case SCons(x, tfun) if p(x) => SCons(x, () => tfun() filter p)
     *   case SCons(x, tfun) => tfun() filter p
     *   case SNil() => SNil()
     * }
     */
  }

  case class SCons[T](x: T, tailFun: () => Stream[T]) extends Stream[T]
  case class SNil[T]() extends Stream[T]

  def natStream(x: BigInt): Stream[BigInt] = SCons(x, () => natStream(x+1))
}
