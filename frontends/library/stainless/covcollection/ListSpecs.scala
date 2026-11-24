package stainless
package covcollection

import lang._
import annotation._
import proof._
import StaticChecks._
import ListOps._

@library
object ListSpecs {

  @opaque
  def snocIndex[T](l: List[T], t: T, i: BigInt): Unit = {
    require(0 <= i && i < l.bsize + 1)
    decreases(l)
    l match {
      case Nil => ()
      case x :: xs => if (i > 0) snocIndex[T](xs, t, i-1) else ()
    }
  }.ensuring(_ => (l :+ t).bapply(i) == (if (i < l.bsize) l.bapply(i) else t))

  @opaque
  def consIndex[T](h: T, t: List[T], i: BigInt): Unit = {
    require(0 <= i && i < t.bsize + 1)
    decreases(t)
    if (!t.isEmpty && i != 0) consIndex(h, t.tail, i-1)
  }.ensuring(_ => (h :: t).bapply(i) == (if (i == 0) h else t.bapply(i - 1)))

  @opaque
  def reverseIndex[T](l: List[T], i: BigInt): Unit = {
    require(0 <= i && i < l.bsize)
    decreases(l)
    l match {
      case Nil => ()
      case x :: xs =>
        snocIndex(xs.reverse, x, i)
        if (i < xs.bsize) {
          consIndex(x, xs, l.bsize - 1 - i)
          reverseIndex[T](xs, i)
        }
    }
  }.ensuring(_ => l.reverse.bapply(i) == l.bapply(l.bsize - 1 - i))

  @opaque
  def snocLast[T](l: List[T], x: T): Unit = {
    decreases(l)
    l match {
      case Nil => ()
      case y :: ys => snocLast(ys, x)
    }
  }.ensuring(_ => (l :+ x).last == x)

  @opaque
  def headReverseLast[T](l: List[T]): Unit = {
    require (!l.isEmpty)
    snocLast(l.tail.reverse, l.head)
  }.ensuring(_ => l.head == l.reverse.last)

  @opaque
  def appendIndex[T](l1: List[T], l2: List[T], i: BigInt): Unit = {
    require(0 <= i && i < l1.bsize + l2.bsize)
    decreases(l1)
    l1 match {
      case Nil => ()
      case x :: xs =>
        if (i != BigInt(0)) appendIndex[T](xs, l2, i - 1)
    }
  }.ensuring(_ => (l1 ++ l2).bapply(i) == (if (i < l1.bsize) l1.bapply(i) else l2.bapply(i - l1.bsize)))

  @opaque
  def appendAssoc[T](@induct l1: List[T], l2: List[T], l3: List[T]): Unit = {
    ()
  }.ensuring(_ => (l1 ++ l2) ++ l3 == l1 ++ (l2 ++ l3))

  @opaque
  def rightUnitAppend[T](@induct l1: List[T]): Unit = {
    ()
  }.ensuring(_ => l1 ++ Nil == l1)

  // This follows immediately from the definition of `++` but we
  // include it here anyway for completeness.
  @opaque
  def leftUnitAppend[T](l1: List[T]): Unit = {
    ()
  }.ensuring(_ => Nil ++ l1 == l1)

  @opaque
  def snocIsAppend[T](l: List[T], t: T): Unit = {
    decreases(l)
    l match {
      case Nil => ()
      case x :: xs => snocIsAppend(xs,t)
    }
  }.ensuring(_ => (l :+ t) == l ++ (t :: Nil))

  @opaque
  def snocAfterAppend[T](l1: List[T], l2: List[T], t: T): Unit = {
    decreases(l1)
    l1 match {
      case Nil => ()
      case x :: xs => snocAfterAppend(xs,l2,t)
    }
  }.ensuring(_ => (l1 ++ l2) :+ t == l1 ++ (l2 :+ t))

  @opaque
  def snocReverse[T](l: List[T], t: T): Unit = {
    decreases(l)
    l match {
      case Nil => ()
      case x :: xs => snocReverse(xs,t)
    }
  }.ensuring(_ => (l :+ t).reverse == t :: l.reverse)

  @opaque
  def reverseReverse[T](l: List[T]): Unit = {
    decreases(l)
    l match {
      case Nil     => ()
      case x :: xs =>
        // (xs.reverse :+ x).reverse == x :: xs.reverse.reverse == x :: xs
        snocReverse[T](xs.reverse, x)
        reverseReverse[T](xs)
    }
  }.ensuring(_ => l.reverse.reverse == l)

  @opaque
  def reverseAppend[T](l1: List[T], l2: List[T]): Unit = {
    decreases(l1)
    l1 match {
      case Nil =>
        // (Nil ++ l2).reverse == l2.reverse == l2.reverse ++ Nil
        rightUnitAppend(l2.reverse)
      case x :: xs =>
        // ((x :: xs) ++ l2).reverse == (xs ++ l2).reverse :+ x
        //                           == (l2.reverse ++ xs.reverse) :+ x
        //                           == l2.reverse ++ (xs.reverse :+ x)
        reverseAppend(xs, l2)
        snocAfterAppend(l2.reverse, xs.reverse, x)
    }
  }.ensuring(_ => (l1 ++ l2).reverse == l2.reverse ++ l1.reverse)

  @opaque
  def snocFoldRight[A, B](xs: List[A], y: A, z: B, f: (A, B) => B): Unit = {
    decreases(xs)
    xs match {
      case Nil => ()
      case x :: xs => snocFoldRight(xs, y, z, f)
    }
  }.ensuring(_ => (xs :+ y).foldRight(z)(f) == xs.foldRight(f(y, z))(f))

  @opaque
  def folds[A, B](xs: List[A], z: B, f: (B, A) => B): Unit = {
    decreases(xs)
    val f2 = (x: A, z: B) => f(z, x)
    xs match {
      case Nil => ()
      case x :: xs =>
        // (x :: xs).foldLeft(z)(f) == xs.foldLeft(f(z, x))(f)
        //                          == xs.reverse.foldRight(f2(x, z))(f2)
        //                          == (xs.reverse :+ x).foldRight(z)(f2)
        folds(xs, f(z, x), f)
        snocFoldRight(xs.reverse, x, z, f2)
    }
  }.ensuring(_ => xs.foldLeft(z)(f) == xs.reverse.foldRight(z)((x: A, z: B) => f(z, x)))

  @opaque
  def scanVsFoldLeft[A, B](l: List[A], z: B, f: (B, A) => B): Unit = {
    decreases(l)
    l match {
      case Nil => ()
      case x :: xs => scanVsFoldLeft(xs, f(z, x), f)
    }
  }.ensuring(_ => l.scanLeft(z)(f).last == l.foldLeft(z)(f))

  @opaque
  def scanVsFoldRight[A,B](@induct l: List[A], z: B, f: (A,B) => B): Unit = {
    ()
  }.ensuring(_ => l.scanRight(z)(f).head == l.foldRight(z)(f))

  @opaque
  def appendContent[A](l1: List[A], l2: List[A]): Unit = {
    ()
  }.ensuring(_ => l1.content ++ l2.content == (l1 ++ l2).content)

  @opaque
  def flattenPreservesContent[T](ls: List[List[T]]): Unit = {
    decreases(ls)
    ls match {
      case Nil => ()
      case h :: t =>
        // flatten(h :: t).content == (h ++ flatten(t)).content
        //                         == h.content ++ flatten(t).content
        //                         == h.content ++ t.foldRight(Set[T]())(f)
        appendContent(h, flatten(t))
        flattenPreservesContent(t)
    }
  }.ensuring(_ => flatten(ls).content[T] == ls.foldRight(Set[T]())((l: List[T], acc: Set[T]) => l.content ++ acc))

  // A lemma about `append` and `updated`
  @opaque
  def appendUpdate[T](l1: List[T], l2: List[T], i: BigInt, y: T): Unit = {
    require(0 <= i && i < l1.bsize + l2.bsize)
    decreases(l1)
    l1 match {
      case Nil => ()
      case x :: xs => if (i == 0) () else appendUpdate[T](xs, l2, i - 1, y)
    }
  }.ensuring(_ =>
    (l1 ++ l2).bupdated(i, y) == (
      if (i < l1.bsize)
        l1.bupdated(i, y) ++ l2
      else
        l1 ++ l2.bupdated(i - l1.bsize, y))
  )

  // a lemma about `append`, `take` and `drop`
  @opaque
  def appendTakeDrop[T](l1: List[T], l2: List[T], n: BigInt): Unit = {
    require(n >= 0)
    decreases(l1)
    l1 match {
      case Nil => ()
      case x :: xs => if (n == 0) () else appendTakeDrop[T](xs, l2, n - 1)
    }
  }.ensuring(_ =>
    ((l1 ++ l2).btake(n) == (
      if (n < l1.bsize) l1.btake(n)
      else if (n > l1.bsize) l1 ++ l2.btake(n - l1.bsize)
      else l1)) &&
      ((l1 ++ l2).bdrop(n) == (
        if (n < l1.bsize) l1.bdrop(n) ++ l2
        else if (n > l1.bsize) l2.bdrop(n - l1.bsize)
        else l2))
  )
  /*
  // A lemma about `append` and `insertAt`
  def appendInsert[T](l1: List[T], l2: List[T], i: BigInt, y: T): Boolean = {
    require(0 <= i && i <= l1.bsize + l2.bsize)
    decreases(l1)

    l1 match {
      case Nil => true
      case x :: xs =>
        if (i == 0) true
        else {
          appendInsert[T](xs, l2, i - 1, y)
          check(
            (xs ++ l2).binsertAt(i - 1, y) == (
              if (i - 1 < xs.bsize) xs.binsertAt(i - 1, y) ++ l2
              else xs ++ l2.binsertAt(i - xs.bsize - 1, y))
          )
        }
    }

    // lemma
    (l1 ++ l2).binsertAt(i, y) == (
      if (i < l1.bsize) l1.binsertAt(i, y) ++ l2
      else l1 ++ l2.binsertAt(i - l1.bsize, y))
  }.holds
  */
  /** A way to apply the forall axiom */
  @opaque
  def applyForAll[T](l: List[T], i: BigInt, p: T => Boolean): Unit = {
    require(i >= 0 && i < l.bsize && l.forall(p))
    decreases(l)
    l match {
      case Nil => ()
      case head :: tail => if (i != 0) applyForAll(tail, i - 1, p)
    }
  }.ensuring(_ => p(l.bapply(i)))

  def listFilterValidProp[A](l: List[A], p: A => Boolean, f: A => Boolean): Unit = {
    require(l.forall(p))
    decreases(l)
    l match {
      case Nil =>
      case x :: xs =>
        assert(xs.forall(p))
        listFilterValidProp(xs, p, f)
    }
 }.ensuring(_ => l.filter(f).forall(p))

  def listAppendValidProp[A](l: List[A], as: List[A], p: A => Boolean): Unit = {
    require(l.forall(p) && as.forall(p))
    decreases(as)
    as match {
      case Nil => ()
      case x :: xs =>
        assert(xs.forall(p))
        listAppendValidProp(l, xs, p)
    }
 }.ensuring(_ => (as ++ l).forall(p))

  @opaque
  def mapPred[A,B](l: List[A], f: A => B, p: B => Boolean): Unit = {
    require(l.forall(a => p(f(a))))
    decreases(l)
    l match {
      case Nil => ()
      case x :: xs =>
        assert(xs.forall(a => p(f(a))))
        mapPred(xs, f, p)
    }
 }.ensuring(_ => l.map(f).forall(p))

  @opaque
  def subsetContains[T](l1: List[T], l2: List[T]): Unit = {
    require(l1.content.subsetOf(l2.content))
    decreases(l1)
    l1 match {
      case Nil => ()
      case x :: xs =>
        assert(xs.content.subsetOf(l2.content))
        subsetContains(xs, l2)
    }
 }.ensuring(_ => l1.forall(l2.contains[T]))

  @inline
  def noDuplicate[T](l: List[T]): Boolean = ListOps.noDuplicate(l)

  @opaque
  def forallContained[T](l: List[T], p: T => Boolean, x: T): Unit = {
    require(l.forall(p) && l.contains(x))
    decreases(l.bsize)
    if (!l.isEmpty && l.tail.contains(x))
      forallContained(l.tail, p, x)

 }.ensuring(_ => p(x))

  @opaque
  def subsetContained[T](l1: List[T], l2: List[T], x: T): Unit = {
    require(l1.forall(l2.contains[T]) && l1.contains(x))
    forallContained(l1, l2.contains[T], x)
 }.ensuring(_ =>
    l2.contains(x)
  )

  def subseq[T](l1: List[T], l2: List[T]): Boolean = {
    decreases(l2.bsize)
    (l1, l2) match {
      case (Nil, _) => true
      case (x :: xs, y :: ys) =>
        (x == y && subseq(xs, ys)) ||
          subseq(l1, ys)
      case _ => false
    }
  }

  def subseqTail[T](l1: List[T], l2: List[T]): Unit = {
    require(!l1.isEmpty && subseq(l1, l2))
    decreases(l2.bsize)

    (l1, l2) match {
      case (x :: xs, y :: ys) =>
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
    decreases(l2.bsize)
    (l1, l2) match {
      case (x :: xs, y :: ys) =>
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
    decreases(l1)
    if (l1.contains(t))
      subseqContains(l1, l2, t)

 }.ensuring(_ =>
    !l1.contains(t)
  )

  @opaque
  def noDuplicateSubseq[T](l1: List[T], l2: List[T]): Unit = {
    decreases(l2.bsize)
    require(subseq(l1, l2) && noDuplicate(l2))

    (l1, l2) match {
      case (Nil, _) =>
        ()
      case (x :: xs, y :: ys) =>
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
    decreases(l2.bsize)
    require(subseq(l1, l2))

    (l1, l2) match {
      case (x :: xs, y :: ys) =>
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
  def containedTail[T](l1: List[T], l2: List[T]): Unit = {
    require(!l2.isEmpty && l1.forall(l2.tail.contains[T]))
    decreases(l1)
    l1 match {
      case Nil => ()
      case x :: xs =>
        assert(xs.forall(l2.tail.contains[T]))
        containedTail(xs, l2)
    }
 }.ensuring(_ =>
    l1.forall(l2.contains[T])
  )

  @opaque
  def subsetRefl[T](l: List[T]): Unit = {
    decreases(l.bsize)
    if (!l.isEmpty) {
      subsetRefl(l.tail)
      containedTail(l.tail, l)
    }
 }.ensuring(_ =>
    l.forall(l.contains[T])
  )

  @opaque
  def forallContainsSubset[T](l1: List[T], l2: List[T]): Unit = {
    require(l1.forall(l2.contains[T]))
    decreases(l1)
    if (!l1.isEmpty) {
      forallContainsSubset(l1.tail, l2) // gives us:
      assert(l1.tail.content.subsetOf(l2.content))
    }
 }.ensuring(_ =>
    l1.content.subsetOf(l2.content)
  )

}
