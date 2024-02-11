/* Copyright 2009-2022 EPFL, Lausanne */

package stainless
package collection

import ListOps._
import lang._
import annotation._
import proof._

@library
object ListSpecs {

  def snocIndex[T](l: List[T], t: T, i: BigInt): Boolean = {
    require(0 <= i && i < l.size + 1)
    decreases(l)
    l match {
      case Nil() => true
      case Cons(x, xs) => if (i > 0) snocIndex[T](xs, t, i-1) else true
    }
    ((l :+ t).apply(i) == (if (i < l.size) l(i) else t))
  }.holds

  @isabelle.lemma(about = "stainless.collection.List.apply")
  def consIndex[T](h: T, t: List[T], i: BigInt): Boolean = {
    require(0 <= i && i < t.size + 1)
    decreases(t)
    check(t.isEmpty || i == 0 || consIndex(h, t.tail, i-1))
    (h :: t).apply(i) == (if (i == 0) h else t.apply(i - 1))
  }.holds

  def reverseIndex[T](l: List[T], i: BigInt): Boolean = {
    require(0 <= i && i < l.size)
    decreases(l)
    l match {
      case Nil() => true
      case Cons(x,xs) =>
        snocIndex(xs.reverse, x, i) &&
        (if (i < xs.size) consIndex(x, xs, l.size - 1 - i) && reverseIndex[T](xs, i) else true)
    }
    l.reverse.apply(i) == l.apply(l.size - 1 - i)
  }.holds

  def snocLast[T](l: List[T], x: T): Boolean = {
    decreases(l)

    l match {
      case Nil() => true
      case Cons(y, ys) => {
        ((y :: ys) :+ x).last   ==| trivial         |
        (y :: (ys :+ x)).last   ==| trivial         |
        (ys :+ x).last          ==| snocLast(ys, x) |
        x
      }.qed
    }

    ((l :+ x).last == x)
  }.holds

  def headReverseLast[T](l: List[T]): Boolean = {
    require (!l.isEmpty)
    (l.head == l.reverse.last)
  }.holds because {
    val Cons(x, xs) = l: @unchecked;
    {
      (x :: xs).head           ==| trivial                 |
      x                        ==| snocLast(xs.reverse, x) |
      (xs.reverse :+ x).last   ==| trivial                 |
      (x :: xs).reverse.last
    }.qed
  }

  def appendIndex[T](l1: List[T], l2: List[T], i: BigInt): Boolean = {
    require(0 <= i && i < l1.size + l2.size)
    decreases(l1)
    l1 match {
      case Nil() => true
      case Cons(x,xs) =>
        (i != BigInt(0)) ==> appendIndex[T](xs, l2, i - 1)
    }
    (l1 ++ l2).apply(i) == (if (i < l1.size) l1(i) else l2(i - l1.size))
  }.holds

  def appendAssoc[T](@induct l1: List[T], l2: List[T], l3: List[T]): Boolean = {
    (l1 ++ l2) ++ l3 == l1 ++ (l2 ++ l3)
  }.holds

  def rightUnitAppend[T](@induct l1: List[T]): Boolean = {
    l1 ++ Nil() == l1
  }.holds

  // This follows immediately from the definition of `++` but we
  // include it here anyway for completeness.
  def leftUnitAppend[T](l1: List[T]): Boolean = {
    Nil() ++ l1 == l1
  }.holds

  def snocIsAppend[T](l: List[T], t: T): Boolean = {
    decreases(l)
    l match {
      case Nil() => true
      case Cons(x,xs) => snocIsAppend(xs,t)
    }
    (l :+ t) == l ++ Cons[T](t, Nil())
  }.holds

  def snocAfterAppend[T](l1: List[T], l2: List[T], t: T): Boolean = {
    decreases(l1)
    l1 match {
      case Nil() => true
      case Cons(x,xs) => snocAfterAppend(xs,l2,t)
    }
    (l1 ++ l2) :+ t == l1 ++ (l2 :+ t)
  }.holds

  def snocReverse[T](l: List[T], t: T): Boolean = {
    decreases(l)
    l match {
      case Nil() => true
      case Cons(x,xs) => snocReverse(xs,t)
    }
    (l :+ t).reverse == Cons(t, l.reverse)
  }.holds

  def reverseReverse[T](l: List[T]): Boolean = {
    decreases(l)
    l match {
      case Nil()       => trivial
      case Cons(x, xs) => {
        (xs.reverse :+ x).reverse ==| snocReverse[T](xs.reverse, x) |
        x :: xs.reverse.reverse   ==| reverseReverse[T](xs)         |
        (x :: xs)
      }.qed
    }
    l.reverse.reverse == l
  }.holds

  def reverseAppend[T](l1: List[T], l2: List[T]): Boolean = {
    decreases(l1)
    l1 match {
      case Nil() => {
        (Nil() ++ l2).reverse         ==| trivial                     |
        l2.reverse                    ==| rightUnitAppend(l2.reverse) |
        l2.reverse ++ Nil()           ==| trivial                     |
        l2.reverse ++ Nil().reverse
      }.qed
      case Cons(x, xs) => {
        ((x :: xs) ++ l2).reverse         ==| trivial               |
        (x :: (xs ++ l2)).reverse         ==| trivial               |
        (xs ++ l2).reverse :+ x           ==| reverseAppend(xs, l2) |
        (l2.reverse ++ xs.reverse) :+ x   ==|
          snocAfterAppend(l2.reverse, xs.reverse, x)                |
        l2.reverse ++ (xs.reverse :+ x)   ==| trivial               |
        l2.reverse ++ (x :: xs).reverse
      }.qed
    }
    (l1 ++ l2).reverse == l2.reverse ++ l1.reverse
  }.holds

  def snocFoldRight[A, B](xs: List[A], y: A, z: B, f: (A, B) => B): Boolean = {
    decreases(xs)
    xs match {
      case Nil() => true
      case Cons(x, xs) => snocFoldRight(xs, y, z, f)
    }
    (xs :+ y).foldRight(z)(f) == xs.foldRight(f(y, z))(f)
  }.holds

  def folds[A, B](xs: List[A], z: B, f: (B, A) => B): Boolean = {
    decreases(xs)
    val f2 = (x: A, z: B) => f(z, x)
    ( xs.foldLeft(z)(f) == xs.reverse.foldRight(z)(f2) ) because {
      xs match {
        case Nil() => true
        case Cons(x, xs) => {
          (x :: xs).foldLeft(z)(f)              ==| trivial               |
          xs.foldLeft(f(z, x))(f)               ==| folds(xs, f(z, x), f) |
          xs.reverse.foldRight(f(z, x))(f2)     ==| trivial               |
          xs.reverse.foldRight(f2(x, z))(f2)    ==|
            snocFoldRight(xs.reverse, x, z, f2)                           |
          (xs.reverse :+ x).foldRight(z)(f2)    ==| trivial               |
          (x :: xs).reverse.foldRight(z)(f2)
        }.qed
      }
    }
  }.holds

  def scanVsFoldLeft[A, B](l: List[A], z: B, f: (B, A) => B): Boolean = {
    decreases(l)
    l match {
      case Nil() => true
      case Cons(x, xs) => scanVsFoldLeft(xs, f(z, x), f)
    }
    ( l.scanLeft(z)(f).last == l.foldLeft(z)(f) )
  }.holds

  def scanVsFoldRight[A,B](@induct l: List[A], z: B, f: (A,B) => B): Boolean = {
    l.scanRight(z)(f).head == l.foldRight(z)(f)
  }.holds

  def appendContent[A](l1: List[A], l2: List[A]) = {
    l1.content ++ l2.content == (l1 ++ l2).content
  }.holds

  def flattenPreservesContent[T](ls: List[List[T]]): Boolean = {
    decreases(ls)
    val f: (List[T], Set[T]) => Set[T] = _.content ++ _
    ( flatten(ls).content == ls.foldRight(Set[T]())(f) ) because {
      ls match {
        case Nil() => true
        case Cons(h, t) => {
          flatten(h :: t).content                     ==| trivial                       |
          (h ++ flatten(t)).content                   ==| appendContent(h, flatten(t))  |
          h.content ++ flatten(t).content             ==| flattenPreservesContent(t)    |
          h.content ++ t.foldRight(Set[T]())(f)       ==| trivial                       |
          f(h, Set[T]()) ++ t.foldRight(Set[T]())(f)  ==| trivial                       |
          (h :: t).foldRight(Set[T]())(f)
        }.qed
      }
    }
  }.holds

  // A lemma about `append` and `updated`
  def appendUpdate[T](l1: List[T], l2: List[T], i: BigInt, y: T): Boolean = {
    require(0 <= i && i < l1.size + l2.size)
    decreases(l1)

    l1 match {
      case Nil() => true
      case Cons(x, xs) => if (i == 0) true else appendUpdate[T](xs, l2, i - 1, y)
    }

    // lemma
    ((l1 ++ l2).updated(i, y) == (
      if (i < l1.size)
        l1.updated(i, y) ++ l2
      else
        l1 ++ l2.updated(i - l1.size, y)))
  }.holds

  // a lemma about `append`, `take` and `drop`
  def appendTakeDrop[T](l1: List[T], l2: List[T], n: BigInt): Boolean = {
    decreases(l1)
    l1 match {
      case Nil() => true
      case Cons(x, xs) => if (n <= 0) true else appendTakeDrop[T](xs, l2, n - 1)
    }
    // lemma
    ((l1 ++ l2).take(n) == (
      if (n < l1.size) l1.take(n)
      else if (n > l1.size) l1 ++ l2.take(n - l1.size)
      else l1)) &&
      ((l1 ++ l2).drop(n) == (
        if (n < l1.size) l1.drop(n) ++ l2
        else if (n > l1.size) l2.drop(n - l1.size)
        else l2))
  }.holds

  // A lemma about `append` and `insertAt`
  def appendInsert[T](l1: List[T], l2: List[T], i: BigInt, y: T): Boolean = {
    require(0 <= i && i <= l1.size + l2.size)
    decreases(l1)

    l1 match {
      case Nil() => true
      case Cons(x, xs) => if (i == 0) true else appendInsert[T](xs, l2, i - 1, y)
    }

    // lemma
    (l1 ++ l2).insertAt(i, y) == (
      if (i < l1.size) l1.insertAt(i, y) ++ l2
      else l1 ++ l2.insertAt(i - l1.size, y))
  }.holds

  /** A way to apply the forall axiom */
  def applyForAll[T](l: List[T], i: BigInt, p: T => Boolean): Boolean = {
    require(i >= 0 && i < l.length && l.forall(p))
    decreases(l)

    l match {
      case Nil() => trivial
      case Cons(head, tail) => if(i == 0) p(head) else applyForAll(l.tail, i - 1, p)
    }

    p(l(i))
  }.holds

  def listFilterValidProp[A](@induct l: List[A], p: A => Boolean, f: A => Boolean): Unit = {
    require(l.forall(p))

  }.ensuring(_ => l.filter(f).forall(p))

  def listAppendValidProp[A](l: List[A], @induct as: List[A], p: A => Boolean): Unit = {
    require(l.forall(p) && as.forall(p))

  }.ensuring(_ => (as ++ l).forall(p))

  @opaque
  def mapPred[A,B](@induct l: List[A], f: A => B, p: B => Boolean): Unit = {
    require(l.forall(a => p(f(a))))

  }.ensuring(_ => l.map(f).forall(p))

  @opaque
  def subsetContains[T](@induct l1: List[T], l2: List[T]): Unit = {
    require(l1.content.subsetOf(l2.content))

  }.ensuring(_ => l1.forall(l2.contains))

  @inline
  def noDuplicate[T](l: List[T]): Boolean = ListOps.noDuplicate(l)

  @opaque
  def forallContained[T](l: List[T], p: T => Boolean, x: T): Unit = {
    require(l.forall(p) && l.contains(x))
    decreases(l)

    if (!l.isEmpty && l.tail.contains(x))
      forallContained(l.tail, p, x)

  }.ensuring(_ => p(x))

  @opaque
  def subsetContained[T](l1: List[T], l2: List[T], x: T): Unit = {
    require(l1.forall(l2.contains) && l1.contains(x))

    forallContained(l1, l2.contains, x)

  }.ensuring(_ =>
    l2.contains(x)
  )

  def subseq[T](l1: List[T], l2: List[T]): Boolean = {
    decreases((l1, l2))
    (l1, l2) match {
      case (Nil(), _) => true
      case (Cons(x, xs), Cons(y, ys)) =>
        (x == y && subseq(xs, ys)) ||
          subseq(l1, ys)
      case _ => false
    }
  }

  def subseqTail[T](l1: List[T], l2: List[T]): Unit = {
    require(!l1.isEmpty && subseq(l1, l2))
    decreases((l1, l2))

    (l1, l2) match {
      case (Cons(x, xs), Cons(y, ys)) =>
        if (subseq(l1, ys))
          subseqTail(l1, ys)
        else if (!xs.isEmpty)
          subseqTail(xs, ys)
      case _ =>
        ()
    }

  }.ensuring(_ =>
    subseq(l1.tail, l2)
  )

  @opaque
  def subseqContains[T](l1: List[T], l2: List[T], t: T): Unit = {
    require(subseq(l1, l2) && l1.contains(t))
    decreases((l1, l2))

    (l1, l2) match {
      case (Cons(x, xs), Cons(y, ys)) =>
        if (subseq(l1, ys))
          subseqContains(l1, ys, t)
        else if (x != t)
          subseqContains(xs, ys, t)
      case _ =>
        ()
    }

  }.ensuring(_ =>
    l2.contains(t)
  )

  @opaque
  def subseqNotContains[T](l1: List[T], l2: List[T], t: T): Unit = {
    require(subseq(l1, l2) && !l2.contains(t))

    if (l1.contains(t))
      subseqContains(l1, l2, t)

  }.ensuring(_ =>
    !l1.contains(t)
  )

  @opaque
  def noDuplicateSubseq[T](l1: List[T], l2: List[T]): Unit = {
    require(subseq(l1, l2) && noDuplicate(l2))
    decreases((l1, l2))

    (l1, l2) match {
      case (Nil(), _) =>
        ()
      case (Cons(x, xs), Cons(y, ys)) =>
        if (subseq(l1, ys)) {
          noDuplicateSubseq(l1, ys)
          check(noDuplicate(l1))
          ()
        } else {
          assert(x == y)
          noDuplicateSubseq(xs, ys)
          assert(noDuplicate(xs))
          assert(subseq(xs, ys))
          assert(!ys.contains(x))
          subseqNotContains(xs, ys, x)
          check(noDuplicate(l1))
          ()
        }
      case _ =>
        ()
    }
  }.ensuring(_ =>
    noDuplicate(l1)
  )

  @opaque
  def mapSubseq[A, B](l1: List[A], l2: List[A], f: A => B): Unit = {
    require(subseq(l1, l2))
    decreases(l2)

    (l1, l2) match {
      case (Cons(x, xs), Cons(y, ys)) =>
        if (subseq(l1, ys))
          mapSubseq(l1, ys, f)
        else
          mapSubseq(xs, ys, f)
      case _ =>
        ()
    }

  }.ensuring(_ => subseq(l1.map(f), l2.map(f)))

  @opaque
  def filterSubseq[A](@induct l: List[A], p: A => Boolean): Unit = {

  }.ensuring(_ => subseq(l.filter(p), l))

  @opaque
  def noDuplicateMapFilter[A, B](l: List[A], p: A => Boolean, f: A => B): Unit = {
    require(noDuplicate(l.map(f)))

    filterSubseq(l, p)
    mapSubseq(l.filter(p), l, f)
    noDuplicateSubseq(l.filter(p).map(f), l.map(f))

  }.ensuring(_ =>
    noDuplicate(l.filter(p).map(f))
  )

  @opaque
  def filterMapNotIn[A, B](@induct l: List[(A, B)], a: A): Unit = {

  }.ensuring(_ =>
    !l.filter(_._1 != a).map(_._1).contains(a)
  )

  @opaque
  def containedTail[T](@induct l1: List[T], l2: List[T]): Unit = {
    require(!l2.isEmpty && l1.forall(l2.tail.contains))

  }.ensuring(_ =>
    l1.forall(l2.contains)
  )

  @opaque
  def subsetRefl[T](l: List[T]): Unit = {
    decreases(l)
    if (!l.isEmpty) {
      subsetRefl(l.tail)
      containedTail(l.tail, l)
    }
  }.ensuring(_ =>
    l.forall(l.contains)
  )

  @opaque
  def forallContainsSubset[T](l1: List[T], l2: List[T]): Unit = {
    require(l1.forall(l2.contains))
    decreases(l1)
    if (!l1.isEmpty) {
      forallContainsSubset(l1.tail, l2) // gives us:
      assert(l1.tail.content.subsetOf(l2.content))
    }
  }.ensuring(_ =>
    l1.content.subsetOf(l2.content)
  )

}
