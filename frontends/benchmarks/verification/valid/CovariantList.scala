/* Copyright 2009-2021 EPFL, Lausanne */

import stainless._
import stainless.lang._
import stainless.annotation._
import stainless.math._
import stainless.proof._

object CovariantList {
  sealed abstract class Option[+T] {
    def get: T = {
      require(!isEmpty)
      (this : @unchecked) match {
        case Some(x) => x
      }
    }

    def isEmpty = this == None

    def orElse[T1 >: T](alternative: => Option[T1]): Option[T1] =
      if (!isEmpty) this else alternative
  }

  case class Some[+T](value: T) extends Option[T]
  case object None extends Option[Nothing]

  sealed abstract class List[+T] {

    def ::[T1 >: T](h: T1): List[T1] = new ::(h, this)

    def size: BigInt = (this match {
      case Nil => BigInt(0)
      case h :: t => 1 + t.size
    }) ensuring (_ >= 0)

    def length = size

    def content[T1 >: T]: Set[T1] = this match {
      case Nil => Set()
      case h :: t => Set[T1](h) ++ t.content
    }

    def contains[T1 >: T](v: T1): Boolean = (this match {
      case h :: t => h == v || t.contains(v)
      case Nil => false
    }) ensuring { _ == (content contains v) }

    def ++[T1 >: T](that: List[T1]): List[T1] = (this match {
      case Nil => that
      case x :: xs => x :: (xs ++ that)
    }) ensuring { res =>
      (res.content == this.content ++ that.content) &&
      (res.size == this.size + that.size) &&
      (that != Nil || res == this)
    }

    def head: T = {
      require(this != Nil)
      val h :: _ = this
      h
    }

    def tail: List[T] = {
      require(this != Nil)
      val _ :: t = this
      t
    }

    def apply(index: BigInt): T = {
      require(0 <= index && index < size)
      if (index == BigInt(0)) {
        head
      } else {
        tail(index-1)
      }
    }

    def :+[T1 >: T](t: T1): List[T1] = {
      this match {
        case Nil => t :: this
        case x :: xs => x :: (xs :+ t)
      }
    } ensuring(res => (res.size == size + 1) && (res.content == content ++ Set(t)))

    def reverse: List[T] = {
      this match {
        case Nil => this
        case x :: xs => xs.reverse :+ x
      }
    } ensuring (res => (res.size == size) && (res.content == content))

    def take(i: BigInt): List[T] = { (this, i) match {
      case (Nil, _) => Nil
      case (h :: t, i) =>
        if (i <= BigInt(0)) {
          Nil
        } else {
          h :: t.take(i-1)
        }
    }} ensuring { res =>
      res.content.subsetOf(this.content) && (res.size == (
        if      (i <= 0)         BigInt(0)
        else if (i >= this.size) this.size
        else                     i
      ))
    }

    def drop(i: BigInt): List[T] = { (this, i) match {
      case (Nil, _) => Nil
      case (h :: t, i) =>
        if (i <= BigInt(0)) {
          h :: t
        } else {
          t.drop(i-1)
        }
    }} ensuring { res =>
      res.content.subsetOf(this.content) && (res.size == (
        if      (i <= 0)         this.size
        else if (i >= this.size) BigInt(0)
        else                     this.size - i
      ))
    }

    def zip[B](that: List[B]): List[(T, B)] = { (this, that) match {
      case (h1 :: t1, h2 :: t2) =>
        (h1, h2) :: t1.zip(t2)
      case _ =>
        Nil
    }} ensuring { _.size == (
      if (this.size <= that.size) this.size else that.size
    )}

    def indexOf[T1 >: T](elem: T1): BigInt = { this match {
      case Nil => BigInt(-1)
      case h :: t if h == elem => BigInt(0)
      case h :: t =>
        val rec = t.indexOf(elem)
        if (rec == BigInt(-1)) BigInt(-1)
        else rec + 1
    }} ensuring { res =>
      (res >= 0) == content.contains(elem)
    }

    def init: List[T] = {
      require(!isEmpty)
      (this : @unchecked) match {
        case h :: Nil =>
          Nil
        case h :: t =>
          h :: t.init
      }
    } ensuring ( (r: List[T]) =>
      r.size == this.size - 1 &&
      r.content.subsetOf(this.content)
    )

    def last: T = {
      require(!isEmpty)
      (this : @unchecked) match {
        case h :: Nil => h
        case _ :: t => t.last
      }
    } ensuring { (res: T) => this.contains(res) }

    def lastOption: Option[T] = { this match {
      case h :: t =>
        t.lastOption.orElse(Some(h))
      case Nil =>
        None
    }} ensuring { _.isEmpty == this.isEmpty }

    def headOption: Option[T] = { this match {
      case h :: t =>
        Some(h)
      case Nil =>
        None
    }} ensuring { _.isEmpty == this.isEmpty }

    def tailOption: Option[List[T]] = { this match {
      case h :: t =>
        Some(t)
      case Nil =>
        None
    }} ensuring { _.isEmpty == this.isEmpty }

    def distinct: List[T] = this match {
      case Nil => Nil
      case h :: t =>
        h :: t.distinct.filter(_ != h)
    }

    def splitAt(index: BigInt): (List[T], List[T]) = (this match {
      case Nil => (Nil, Nil)
      case h :: rest => {
        if (index <= BigInt(0)) {
          (Nil, this)
        } else {
          val (left, right) = rest splitAt (index - 1)
          (h :: left, right)
        }
      }
    }) ensuring { (res: (List[T], List[T])) =>
      res._1 ++ res._2 == this &&
      res._1 == take(index) && res._2 == drop(index)
    }

    def updated[T1 >: T](i: BigInt, y: T1): List[T1] = {
      require(0 <= i && i < this.size)
      this match {
        case x :: tail if i == 0 =>
          y :: tail
        case x :: tail =>
          x :: tail.updated(i - 1, y)
      }
    }

    def rotate(s: BigInt): List[T] = {
      if (isEmpty) {
        Nil
      } else {
        drop(s mod size) ++ take(s mod size)
      }
    } ensuring { res =>
      res.size == this.size
    }

    def isEmpty = this == Nil

    def nonEmpty = !isEmpty

    // Higher-order API
    def map[R](f: T => R): List[R] = { this match {
      case Nil => Nil
      case h :: t => f(h) :: t.map(f)
    }} ensuring { _.size == this.size }

    def foldLeft[R](z: R)(f: (R,T) => R): R = this match {
      case Nil => z
      case h :: t => t.foldLeft(f(z,h))(f)
    }

    def foldRight[R](z: R)(f: (T,R) => R): R = this match {
      case Nil => z
      case h :: t => f(h, t.foldRight(z)(f))
    }

    def scanLeft[R](z: R)(f: (R,T) => R): List[R] = { this match {
      case Nil => z :: Nil
      case h :: t => z :: t.scanLeft(f(z,h))(f)
    }} ensuring { !_.isEmpty }

    def scanRight[R](z: R)(f: (T,R) => R): List[R] = { this match {
      case Nil => z :: Nil
      case h :: t =>
        val rest @ (h1 :: _) = t.scanRight(z)(f)
        f(h, h1) :: rest
    }} ensuring { !_.isEmpty }

    def flatMap[R](f: T => List[R]): List[R] = this match {
      case Nil => Nil
      case x :: xs => f(x) ++ (xs flatMap f)
    }

    def filter(p: T => Boolean): List[T] = { this match {
      case Nil => Nil
      case h :: t if p(h) => h :: t.filter(p)
      case _ :: t => t.filter(p)
    }} ensuring { res =>
      res.size <= this.size &&
      res.content.subsetOf(this.content) &&
      res.forall(p)
    }

    def filterNot(p: T => Boolean): List[T] =
      filter(!p(_)) ensuring { res =>
        res.size <= this.size &&
        res.content.subsetOf(this.content) &&
        res.forall(!p(_))
      }

    def partition(p: T => Boolean): (List[T], List[T]) = { this match {
      case Nil => (Nil, Nil)
      case h :: t =>
        val (l1, l2) = t.partition(p)
        if (p(h)) (h :: l1, l2)
        else      (l1, h :: l2)
    }} ensuring { res =>
      res._1 == filter(p) &&
      res._2 == filterNot(p)
    }

    // In case we implement for-comprehensions
    def withFilter(p: T => Boolean) = filter(p)

    def forall(p: T => Boolean): Boolean = this match {
      case Nil => true
      case h :: t => p(h) && t.forall(p)
    }

    def exists(p: T => Boolean) = !forall(!p(_))

    def find(p: T => Boolean): Option[T] = { this match {
      case Nil => None
      case h :: t => if (p(h)) Some(h) else t.find(p)
    }} ensuring { res => res match {
      case Some(r) => (content contains r) && p(r)
      case None => true
    }}

    def takeWhile(p: T => Boolean): List[T] = { this match {
      case h :: t if p(h) => h :: t.takeWhile(p)
      case _ => Nil
    }} ensuring { res =>
      (res forall p) &&
      (res.size <= this.size) &&
      (res.content subsetOf this.content)
    }

    def dropWhile(p: T => Boolean): List[T] = { this match {
      case h :: t if p(h) => t.dropWhile(p)
      case _ => this
    }} ensuring { res =>
      (res.size <= this.size) &&
      (res.content subsetOf this.content) &&
      (res.isEmpty || !p(res.head))
    }

    def count(p: T => Boolean): BigInt = { this match {
      case Nil => BigInt(0)
      case h :: t =>
        (if (p(h)) BigInt(1) else BigInt(0)) + t.count(p)
    }} ensuring {
      _ == this.filter(p).size
    }

    def indexWhere(p: T => Boolean): BigInt = { this match {
      case Nil => BigInt(-1)
      case h :: _ if p(h) => BigInt(0)
      case _ :: t =>
        val rec = t.indexWhere(p)
        if (rec >= 0) rec + BigInt(1)
        else BigInt(-1)
    }} ensuring {
      _ >= BigInt(0) == (this exists p)
    }


    // FIXME(gsps): This used to work, but a rewriting in `matchToIfThenElse` now inserts
    //   let bindings that make the type checker miss the refinement type of the match's
    //   scrutinee. This could be fixed either by propagating refinement type throughout
    //   Inox's type system, or by inferring types for such lets in TypeChecker.
/*
    // Translation to other collections
    def toSet[T1 >: T]: Set[T1] = foldLeft(Set[T1]()){
      case (current, next) => current ++ Set(next)
    }
*/
  }

  case class ::[+T](h: T, t: List[T]) extends List[T]
  case object Nil extends List[Nothing]
}

