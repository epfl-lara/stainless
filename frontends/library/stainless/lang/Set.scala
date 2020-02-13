/* Copyright 2009-2019 EPFL, Lausanne */

package stainless.lang

import stainless.annotation._
import stainless.collection.List

import scala.language.implicitConversions
import scala.collection.immutable.{Set => ScalaSet}

object Set {

  @library @inline
  def empty[T] = Set[T]()

  @ignore
  def apply[T](elems: T*) = {
    new Set[T](ScalaSet[T](elems : _*))
  }

  @extern @pure @library
  def fromScala[A](set: ScalaSet[A]): Set[A] = {
    new Set(set)
  }

  @extern @pure @library
  def mkString[A](set: Set[A], infix: String)(format: A => String): String = {
    set.theSet.map(format).toList.sorted.mkString(infix)
  }

  @library
  implicit class SetOps[A](val set: Set[A]) extends AnyVal {

    @extern @pure
    def map[B](f: A => B): Set[B] = {
      new Set(set.theSet.map(f))
    } ensuring { res =>
      forall((a: A) => set.contains(a) == res.contains(f(a)))
    }

    @extern @pure
    def filter(p: A => Boolean): Set[A] = {
      new Set(set.theSet.filter(p))
    } ensuring { res =>
      forall((a: A) => if (set.contains(a) && p(a)) res.contains(a) else !res.contains(a))
    }

    @extern @pure
    def withFilter(p: A => Boolean): Set[A] = {
      new Set(set.theSet.filter(p))
    } ensuring { res =>
      forall((a: A) => if (set.contains(a) && p(a)) res.contains(a) else !res.contains(a))
    }

    @extern @pure
    def toList: List[A] = {
      List.fromScala(set.theSet.toList)
    } ensuring { res =>
      forall((a: A) => res.contains(a) == set.contains(a))
    }

    @extern @pure
    def toScala: ScalaSet[A] = set.theSet

    @extern @pure
    def mkString(infix: String)(format: A => String): String = {
      set.theSet.map(format).toList.sorted.mkString(infix)
    }

    def nonEmpty: Boolean = !set.isEmpty
  }
}

@ignore
case class Set[T](theSet: scala.collection.immutable.Set[T]) {

  def +(a: T): Set[T] = new Set[T](theSet + a)
  def ++(a: Set[T]): Set[T] = new Set[T](theSet ++ a.theSet)

  def -(a: T): Set[T] = new Set[T](theSet - a)
  def --(a: Set[T]): Set[T] = new Set[T](theSet -- a.theSet)

  def &(a: Set[T]): Set[T] = new Set[T](theSet & a.theSet)

  def size: BigInt = theSet.size
  def isEmpty: Boolean = theSet.isEmpty

  def contains(a: T): Boolean = theSet.contains(a)
  def subsetOf(b: Set[T]): Boolean = theSet.subsetOf(b.theSet)
}
