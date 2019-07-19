import stainless.collection._
import stainless.lang._
import stainless.annotation._
import stainless.proof._
import Theorem._

object Leftpad {
  def max(b1: BigInt, b2: BigInt) = {
    if (b1 > b2) b1
    else b2
  }

  def appendCons[T](@induct l1: List[T], l2: List[T], x: T) = {
    l1 ++ (x :: l2) == (l1 :+ x) ++ l2
  }.holds

  def fillMore[T](n: BigInt, t: T): Boolean = {
    require(n >= 0)
    decreases(n)
    if (n == 0)
      List.fill(n)(t) :+ t == List.fill(n+1)(t)
    else {
      check(fillMore(n-1,t)) // use the recursive hypothesis
      List.fill(n)(t) :+ t == List.fill(n+1)(t)
    }
  }.holds

  def leftPad[T](c: T, n: BigInt, s: List[T]): List[T] = {
    require(n > 0)
    decreases(max(n-s.length, 0))
    if (s.length < n) {
      leftPad(c, n, c :: s)
    } else {
      s
    }
  }

  def leftPadLemma[T](c: T, n: BigInt, s: List[T]): Boolean = {
    require(n > 0)
    decreases(max(n-s.length, 0))
    val res = leftPad(c,n,s)

    val proof =
      if (s.length < n) {
        val b1 = leftPadLemma(c, n, c :: s)
        val b2 = (res == List.fill(n - s.length - 1)(c) ++ (c :: s)) proveUsing b1 // from the recursive call
        val b3 = appendCons(List.fill(n - s.length - 1)(c), s, c) // invoking the appendCons lemma
        val b4 = (res == (List.fill(n - s.length - 1)(c) :+ c) ++ s) proveUsing (b2 && b3) // thanks to the appendCons lemma
        val b5 = fillMore(n - s.length - 1, c) // invoking the fillMore Lemma
        (res.length == max(n, s.length) &&
        res == List.fill(n - s.length)(c) ++ s) proveUsing (b4 && b5)
      } else {
        prove(
          res.length == max(n, s.length) &&
          res == List.fill(n - s.length)(c) ++ s
        )
      }

    assert(proof)

    res.length == max(n, s.length) &&
    res == List.fill(n - s.length)(c) ++ s
  }.holds
}
