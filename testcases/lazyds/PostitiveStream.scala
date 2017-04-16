package lazyds

import leon._
import lang._
import annotation._
import scala.math.BigInt.int2bigInt

object PosStream {

  sealed abstract class Stream
  private case class SCons(x: BigInt, tailFun: () => Stream) extends Stream

  def posUpto(s: Stream, n: BigInt): Boolean = {
    require(n >= 0)
    s match {
      case SCons(x, tfun) if x > 0 => posUpto(tfun(), n-1)
      case _ => false
    }
  }

  def inc(s: Stream, n: BigInt): Stream = {
    require(n >= 0 && posUpto(s, n))
    s match {
      case SCons(y, tfun) =>
        val tail = tfun()
        SCons(y + 1, () => inc(tail, n-1))
    }
  } ensuring (res => posUpto(res,n))

  // a function that invokes inc a non-deterministic number of times on an initial stream
  def rec(steps: BigInt, c: BigInt, s: Stream): Stream = {
    require(steps >= 0)
    if (c >= 0) {
      rec(steps, c - 1, inc(s, steps))
    } else
      s
  }

  def natStream(n: BigInt): Stream = SCons(n, () => natStream(n+1))

  def client(steps: BigInt, c: BigInt) = {
    require(steps >= 0)
    rec(steps, c, natStream(1))
  }
}
