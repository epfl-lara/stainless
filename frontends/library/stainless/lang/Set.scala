/* Copyright 2009-2021 EPFL, Lausanne */

package stainless.lang

import StaticChecks._
import stainless.annotation._
import stainless.collection.{List, ListOps}

import scala.collection.immutable.{Set => ScalaSet}

object Set {

  @library @inline
  def empty[T] = Set[T]()

  @ignore
  def apply[T](elems: T*) = {
    new Set[T](ScalaSet[T](elems*))
  }

  @extern @pure @library
  def fromScala[A](set: ScalaSet[A]): Set[A] = {
    new Set(set)
  }

  // @extern @pure @library
  // def mkString[A](set: Set[A], infix: String)(format: A => String): String = {
  //   set.theSet.map(format).toList.sorted.mkString(infix)
  // }

  extension[A](set: Set[A]) {

    @library @extern @pure
    def exists(p: A => Boolean): Boolean = {
      set.theSet.exists(p)
    }.ensuring(res => res == set.toList.exists(p))

    @library @extern @pure
    def forall(p: A => Boolean): Boolean = {
      set.theSet.forall(p)
    }.ensuring(res => res == set.toList.forall(p))

    @library @extern @pure
    def map[B](f: A => B): Set[B] = {
      new Set(set.theSet.map(f))
    }

    @library @extern @pure
    def mapPost1[B](f: A => B)(a: A): Unit = {
      ()
    }.ensuring { _ =>
      !set.contains(a) || map[B](f).contains(f(a))
    }
   
    @library @extern @pure
    def mapPost2[B](f: A => B)(b: B): A = {
      require(map[B](f).contains(b))
      (??? : A)
    }.ensuring { (a:A) =>
      b == f(a) && set.contains(a)
    }

    @library @extern @pure
    def flatMap[B](f: A => Set[B]): Set[B] = {
      new Set(set.theSet.flatMap(f(_).theSet))
    }

    @library @extern @pure
    def flatMapPost[B](f: A => Set[B])(b: B) = {
      (??? : A)
    }.ensuring { _ =>
      set.flatMap(f).contains(b) == set.exists(a => f(a).contains(b))
    }

    @library @extern @pure
    def filter(p: A => Boolean): Set[A] = {
      new Set(set.theSet.filter(p))
    }

    @library @extern @pure
    def filterPost(p: A => Boolean)(a: A): Unit = {
      ()
   }.ensuring (_ => filter(p).contains(a) == (p(a) && set.contains(a)))

    @library @extern @pure
    def withFilter(p: A => Boolean): Set[A] = {
      new Set(set.theSet.filter(p))
    }

    @library @extern @pure
    def withFilterPost(p: A => Boolean)(a: A): Unit = {
      ()
   }.ensuring(_ => withFilter(p).contains(a) == (p(a) && set.contains(a)))

    @library @extern @pure @ghost
    def toList: List[A] = {
      List.fromScala(set.theSet.toList)
   }.ensuring(res => ListOps.noDuplicate(res) && res.content == set)

    @library @extern @pure
    def toListPost(a:A): Unit = {
      ()
   }.ensuring(_ => toList.contains(a) == set.contains(a))

    @library @extern @pure
    def toScala: ScalaSet[A] = set.theSet

    @library @extern @pure
    def mkString(infix: String)(format: A => String): String = {
      set.theSet.map(format).toList.sorted.mkString(infix)
    }

    def nonEmpty: Boolean = !set.isEmpty
  }
}

/* 
 Sets are built-in in Stainless trees. Semantics is that they are required to be finite.
 Equality is extensional.
 Maps to finite sets in cvc5, and overraproximated with generalized arrays in z3 (which can also be co-finite).
 Runtime behavior uses default immutable Scala set.
 */
@ignore
sealed case class Set[T](theSet: scala.collection.immutable.Set[T]) {

  def +(a: T): Set[T] = new Set[T](theSet + a)
  def ++(a: Set[T]): Set[T] = new Set[T](theSet ++ a.theSet)

  def -(a: T): Set[T] = new Set[T](theSet - a)
  def --(a: Set[T]): Set[T] = new Set[T](theSet -- a.theSet)

  def &(a: Set[T]): Set[T] = new Set[T](theSet & a.theSet)

  def isEmpty: Boolean = theSet.isEmpty

  def contains(a: T): Boolean = theSet.contains(a)
  def subsetOf(b: Set[T]): Boolean = theSet.subsetOf(b.theSet)
}
