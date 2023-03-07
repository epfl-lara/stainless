import stainless.lang._
import stainless.collection._
import stainless.annotation._

object WhacAFun {
  def andThen1[A, B, C](f: A => B, g: B => C): A => C = a => g(f(a))
  def andThen2[A, B, C](ff: A => B, gg: B => C): A => C = aa => gg(ff(aa))

  def compose1[A, B, C](f: B => C, g: A => B): A => C = a => f(g(a))
  def compose2[A, B, C](ff: B => C, gg: A => B): A => C = aa => ff(gg(aa))

  def flip1[A, B, C](f: (A, B) => C): (B, A) => C = (b, a) => f(a, b)
  def flip2[A, B, C](f: (A, B) => C): (B, A) => C = (b, a) => {val res = f(a, b); res }

  def curry1[A, B, C](f: (A, B) => C): A => B => C = a => b => f(a, b)
  def curry2[A, B, C](f: (A, B) => C): A => B => C = aa => bb => { val res = f(aa, bb); res }

  def uncurry1[A, B, C](f: A => B => C): (A, B) => C = (a, b) => f(a)(b)
  def uncurry2[A, B, C](f: A => B => C): (A, B) => C = (a, b) => { val res = f(a)(b); res }

  /*
  // Times out
  def rep1[A](n: BigInt)(f: A => A)(a: A) = {
    require(n >= 0)
    repeat1(n)(f)(a)
  }
  def rep2[A](n: BigInt)(f: A => A)(a: A) = {
    require(n >= 0)
    repeat2(n)(f)(a)
  }
  // Said to be non-equivalent, even though they are :(
  def repeat1[A](n: BigInt)(f: A => A): A => A = {
    require(n >= 0)
    decreases(n)
    a => {
      if (n == 0) a
      else repeat1(n - 1)(f)(f(a))
    }
  }
  def repeat2[A](n: BigInt)(f: A => A): A => A = {
    require(n >= 0)
    decreases(n)
    if (n == 0) a => a
    else a => repeat2(n - 1)(f)(f(a))
  }
  */

  def repeat1[A](n: BigInt)(f: A => A): A => A = {
    require(n >= 0)
    decreases(n)
    a => {
      if (n == 0) a
      else repeat1(n - 1)(f)(f(a))
    }
  }
  def repeat2[A](n: BigInt)(f: A => A): A => A = {
    require(n >= 0)
    decreases(n)
    a => {
      if (n == 0) a
      else {
        val fa = f(a)
        repeat1(n - 1)(f)(fa)
      }
    }
  }
}