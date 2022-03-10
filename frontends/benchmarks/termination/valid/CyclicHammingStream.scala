
import stainless._
import lang._
import annotation._
import collection._

/**
 * An infinite list of hamming numbers (Brid & Wadler)
 */
object MergeAndHammingNumbers {
  /**
   *  An infinite integer stream
   */
  case class SCons(x: BigInt, tailFun: () => SCons) {
    lazy val tail = tailFun()
  }

  /**
   * A generic lazy higher-order `map` function
   */
  def map(f: BigInt => BigInt, xs: SCons): SCons = {
    xs match {
      case SCons(x, _) =>
        SCons(f(x), () => map(f, xs.tail))
    }
  }

  /**
   * Computes minimum of three elements
   */
  def min(x: BigInt, y: BigInt, z: BigInt) = {
    if(x <= y)
      if(x <= z) x else z
    else
      if(y <= z) y else z
  }

  /**
   * A three way merge function
   */
  def merge(a: SCons, b: SCons, c: SCons): SCons = {
    val m = min(a.x, b.x, c.x)
    SCons(m, () => {
      val nexta = if (a.x == m) a.tail else a
      val nextb = if (b.x == m) b.tail else b
      val nextc = if (c.x == m) c.tail else c
      merge(nexta, nextb, nextc)
    })
  }

  def nthElem(n: BigInt, s: SCons): BigInt = {
    require(n >= 0)
    if (n == 0) s.x
    else {
      nthElem(n - 1, s.tail)
    }
  }

   /**
   * A stream of hamming numbers
   */
  lazy val hamstream: SCons = SCons(1, () => {
    val hs = this.hamstream
    merge(map(2 * _, hs), map(3 * _, hs), map(5 * _, hs))
  })

  /**
   * `nth` hamming number in O(n) time.
   */
  def nthHammingNumber(n: BigInt) = {
    require(n >= 0)
    nthElem(n, hamstream)
  }
}
