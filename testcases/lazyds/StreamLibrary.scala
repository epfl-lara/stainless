package terminationProofs

import leon._
import mem._
import higherorder._
import lang._
import annotation._
//import collection._
import instrumentation._
import invariant._

/**
 * This defines a stream library that does not use memoization.
 * TODO: How will memoization impact termination argument ?
 */
object StreamLibrary {

  sealed abstract class Stream {
    @inline
    def isEmpty: Boolean = this == SNil()

    val tail: Stream = {
      require(!isEmpty)
      this match {
        case SCons(_, tailFun, _) => tailFun()
      }
    }

    val rank = this match {
      case SCons(_, _, r) =>
        if(r >= 0) r else BigInt(0)
      case SNil()         => BigInt(0)
    }

    /**
     * A property that is true if `sz` field decreases for the tail of the stream.
     * `sz` is a well-founded ordering.
     * This is a data structure invariant.
     */
    /*def valid: Boolean = {
      this match {
        case c @ SCons(_, tfun, r) =>
          r >= 1 &&
          (tfun fmatch[Stream,List,Stream,Boolean] {
            case (f, rear, a) if tfun.is(() => rotate(f,rear,a)) =>
              r == f.rank + rear.rank + a.rank + 1 && f.valid && a.valid
            case (a, _, _) if tfun.is(() => id(a)) =>
              r == 1 + a.rank && a.valid
          })
        case _ => true
      }
    }*/

    def size: BigInt = {
      //decreases(this.rank)
      this match {
        case c@SCons(_, _, r) =>
          1 + (c.tail*).size
        case SNil() =>
          BigInt(0)
      }
    } //ensuring(res => this.rank == res) // this property states that `rank` and `size` are equivalent
  }
  case class SCons(x: BigInt, tailFun: () => Stream, sz: BigInt) extends Stream
  case class SNil() extends Stream

  def map(f: BigInt => BigInt, s: Stream): Stream = {
    s match {
      case c@SCons(x, tfun, sz) =>
        val tail = tfun()
        SCons(f(x), () => map(f,tail), sz)
      case SNil() => s
    }
  }

  /**
   * A property that the input stream is finite
   */
  def finiteStream(s: Stream): Boolean = {
    s match {
      case SCons(x, tfun, sz) =>
        val tail = tfun()

    }

  }

  def filter(p: BigInt => Boolean, s: Stream): Stream = {
    require(forall{y: BigInt => f(y) < y && f(y) >= 0})
    s match {
      case c @ SCons(x, tfun) =>
        val tail = tfun()
        if (x >= 0) SCons(x, () => filter(tail))
        else filter(tail)
      case SNil() => s
    }
  }

  private def natStream(n: BigInt): Stream = {
    require(n >= -1)
    if(n == -1) SNil()
    else SCons(n, () => natStream(n-1), n + 1)
  }

  def mainFun(s: Stream) = {
    map(_ + 1, s)
  }
}
