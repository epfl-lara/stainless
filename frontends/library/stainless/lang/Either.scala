/* Copyright 2009-2021 EPFL, Lausanne */

package stainless.lang

import stainless.collection._
import stainless.annotation._
import stainless.lang.StaticChecks._

/**
 * @author Viktor
 */
@library
sealed abstract class Either[A, B] {
  def isLeft: Boolean
  def isRight: Boolean
  def swap: Either[B, A]

  def map[C](f: B => C): Either[A, C] = this match {
    case Left(a)  => Left(a)
    case Right(b) => Right(f(b))
  }

  def flatMap[C](f: B => Either[A, C]): Either[A, C] = this match {
    case Left(a)  => Left(a)
    case Right(b) => f(b)
  }

  def fold[C](fa: A => C, fb: B => C): C = this match {
    case Right(b) => fb(b)
    case Left(a) => fa(a)
  }

  def foreach[U](f: A => U): Unit = this match {
    case Left(a) => f(a)
    case _ => ()
  }

  def getOrElse(or: => A): A = this match {
    case Left(a) => a
    case _ => or
  }

  def orElse(or: => Either[A, B]): Either[A, B] = this match {
    case Right(_) => this
    case _ => or
  }

  def contains[B1 >: B](elem: B1): Boolean = this match {
    case Right(b) => b == elem
    case _ => false
  }

  def forall(f: B => Boolean): Boolean = this match {
    case Right(b) => f(b)
    case _ => true
  }

  def exists(p: B => Boolean): Boolean = this match {
    case Right(b) => p(b)
    case _ => false
  }

  def filterOrElse(p: B => Boolean, zero: => A): Either[A, B] = this match {
    case Right(b) if !p(b) => Left(zero)
    case _ => this
  }

  def toOption: Option[B] = this match {
    case Right(b) => Some(b)
    case _ => None()
  }

  def toList: List[B] = this match {
    case Right(b) => List(b)
    case _ => Nil()
  }

  def get: B = {
    require(isRight)
    val Right(value) = this: @unchecked
    value
  }

  def left: Either.LeftProjection[A, B] = Either.LeftProjection(this)
}

@library
case class Left[A,B](content: A) extends Either[A,B] {
  def isLeft  = true
  def isRight = false
  def swap    = Right[B, A](content)
}

@library
case class Right[A,B](content: B) extends Either[A,B] {
  def isLeft  = false
  def isRight = true
  def swap    = Left[B, A](content)
}

object Either {
  @library
  implicit class MergeableEither[A](e: Either[A, A]) {
    def merge: A = e match {
      case Left(a) => a
      case Right(a) => a
    }
  }

  @library
  implicit class FlattenableEither[A, B](e: Either[Either[A, B], B]) {
    def flatten: Either[A, B] = e match {
      case Left(l) => l
      case Right(r) => Right(r)
    }
  }

  @library
  case class LeftProjection[A, B](e: Either[A, B]) {
    def foreach[U](f: A => U): Unit = e match {
      case Left(a) => f(a)
      case Right(_) => ()
    }

    def getOrElse(or: => A): A = e match {
      case Left(a) => a
      case Right(_) => or
    }

    def forall(p: A => Boolean): Boolean = e match {
      case Left(a) => p(a)
      case Right(_) => true
    }

    def exists(p: A => Boolean): Boolean = e match {
      case Left(a) => p(a)
      case Right(_) => false
    }

    def flatMap[A1](f: A => Either[A1, B]): Either[A1, B] = e match {
      case Left(a) => f(a)
      case Right(b) => Right(b)
    }

    def map[A1](f: A => A1): Either[A1, B] = e match {
      case Left(a) => Left(f(a))
      case Right(b) => Right(b)
    }

    def filterToOption[B1](p: A => Boolean): Option[Either[A, B1]] = e match {
      case Left(a) if p(a) => Some(Left(a))
      case _ => None()
    }

    def toList: List[A] = e match {
      case Left(a) => List(a)
      case Right(_) => List.empty
    }

    def toOption: Option[A] = e match {
      case Left(a) => Some(a)
      case Right(_) => None()
    }
  }
}