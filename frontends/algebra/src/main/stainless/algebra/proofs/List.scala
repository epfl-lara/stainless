package stainless.algebra
package proofs

import stainless.lang._
import stainless.proof._
import stainless.annotation._
import stainless.collection._

object List {

  @library
  def foldLeftEqualsFoldRight[A](xs: List[A])(implicit M: Monoid[A]): Boolean = {
    decreases(xs.size)

    (xs.foldLeft(M.identity)(M.combine) == xs.foldRight(M.identity)(M.combine)) because {
      xs match {
        case Nil() => {
          Nil[A]().foldLeft(M.identity)(M.combine)   ==| trivial |
          M.identity                                 ==| trivial |
          Nil[A]().foldRight(M.identity)(M.combine)
        }.qed
        case Cons(y, Nil()) => {
          Cons(y, Nil[A]()).foldLeft(M.identity)(M.combine)       ==| trivial                  |
          Nil[A]().foldLeft(M.combine(M.identity, y))(M.combine)  ==| M.law_leftIdentity(y)    |
          Nil[A]().foldLeft(y)(M.combine)                         ==| trivial                  |
          y                                                       ==| M.law_rightIdentity(y)   |
          M.combine(y, M.identity)                                ==| trivial                  |
          M.combine(y, Nil[A]().foldRight(M.identity)(M.combine)) ==| trivial                  |
          Cons(y, Nil[A]()).foldRight(M.identity)(M.combine)
        }.qed
        case Cons(y1, Cons(y2, ys)) =>
          assert((y1 :: y2 :: ys).foldLeft(M.identity)(M.combine) == (y2 :: ys).foldLeft(M.combine(M.identity, y1))(M.combine))
          assert(M.law_leftIdentity(y1))
          assert((y2 :: ys).foldLeft(M.combine(M.identity, y1))(M.combine) == (y2 :: ys).foldLeft(y1)(M.combine))
          assert((y2 :: ys).foldLeft(y1)(M.combine) == ys.foldLeft(M.combine(y1, y2))(M.combine))
          assert(M.law_leftIdentity(M.combine(y1, y2)))
          assert(ys.foldLeft(M.combine(y1, y2))(M.combine) == ys.foldLeft(M.combine(M.identity, M.combine(y1, y2)))(M.combine))
          assert(ys.foldLeft(M.combine(M.identity, M.combine(y1, y2)))(M.combine) == (M.combine(y1, y2) :: ys).foldLeft(M.identity)(M.combine))
          assert((M.combine(y1, y2) :: ys).size < (y1 :: y2 :: ys).size)
          assert(foldLeftEqualsFoldRight(M.combine(y1, y2) :: ys))
          assert((M.combine(y1, y2) :: ys).foldLeft(M.identity)(M.combine) == (M.combine(y1, y2) :: ys).foldRight(M.identity)(M.combine))
          assert((M.combine(y1, y2) :: ys).foldRight(M.identity)(M.combine) == M.combine(M.combine(y1, y2), ys.foldRight(M.identity)(M.combine)))
          assert(M.law_associativity(y1, y2, ys.foldRight(M.identity)(M.combine)))
          assert(M.combine(M.combine(y1, y2), ys.foldRight(M.identity)(M.combine)) == M.combine(y1, M.combine(y2, ys.foldRight(M.identity)(M.combine))))
          assert(M.combine(y1, M.combine(y2, ys.foldRight(M.identity)(M.combine))) == M.combine(y1, (y2 :: ys).foldRight(M.identity)(M.combine)))
          assert(M.combine(y1, (y2 :: ys).foldRight(M.identity)(M.combine)) == (y1 :: y2 :: ys).foldRight(M.identity)(M.combine))
          check((y1 :: y2 :: ys).foldLeft(M.identity)(M.combine) == (y1 :: y2 :: ys).foldRight(M.identity)(M.combine))
      }
    }
  }.holds
}

