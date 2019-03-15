/* From ESOP 2014, Kuwahara et al */

import stainless.lang._
import stainless.collection._

object MapBenchmark {

  def map[T,U](list: List[T], f: T => U): List[U] = {
    decreases(list)
    list match {
      case Cons(x, xs) => Cons(f(x), map(xs, f))
      case Nil() => Nil()
    }
  }

  def compose[T,U,V](f: U => V, g: T => U): T => V = (x: T) => f(g(x))

  def add(x: BigInt)(y: BigInt) = x + y

  def main(list: List[BigInt]) = map(list, compose(add(1), add(2)))
}
