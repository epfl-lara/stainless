package stainless
package algebra
package ops

import stainless.lang._
import stainless.annotation._
import stainless.collection.ConcRope._

object ConcRope {

  @library
  implicit class ConcRopeOps[A](val conc: Conc[A]) extends AnyVal {
    @library
    final def foldMap[B](f: A => B)(implicit M: Monoid[B]): B = {
      decreases(conc)
      conc match {
        case Empty()             => M.identity
        case Single(x)           => f(x)
        case CC(left, right)     => M.combine(left.foldMap(f), right.foldMap(f))
        case Append(left, right) => M.combine(left.foldMap(f), right.foldMap(f))
      }
    }
  }
}

// def foldMap[R](f: T => R)(implicit M: Monoid[R]): R = {
//   map(f).foldLeft(M.identity)(M.combine)
// }
