package stainless
package covcollection

import annotation._
import lang.Set
import lang.StaticChecks._

@library
sealed abstract class Option[+T] {

  def get: T = {
    require(this.isDefined)
    (this : @unchecked) match {
      case Some(x) => x
    }
  }

  def getOrElse[TT >: T](default: => TT): TT = this match {
    case Some(v) => v
    case None  => default
  }

  def orElse[TT >: T](or: => Option[TT]): Option[TT] = { this match {
    case Some(v) => this
    case None => or
  }} ensuring {
    _.isDefined == this.isDefined || or.isDefined
  }

  def isEmpty: Boolean = this match {
    case Some(_) => false
    case None => true
  }

  def nonEmpty: Boolean  = !isEmpty

  def isDefined: Boolean = !isEmpty


  // Higher-order API
  def map[R](f: T => R): Option[R] = { this match {
    case None => None
    case Some(x) => Some(f(x))
  }} ensuring { _.isDefined == this.isDefined }

  def flatMap[R](f: T => Option[R]): Option[R] = this match {
    case None => None
    case Some(x) => f(x)
  }

  def filter(p: T => Boolean): Option[T] = this match {
    case Some(x) if p(x) => Some(x)
    case _ => None
  }

  def withFilter(p: T => Boolean): Option[T] = filter(p)

  def forall(p: T => Boolean) = this match {
    case Some(x) if !p(x) => false
    case _ => true
  }

  def exists(p: T => Boolean) = !forall(!p(_))

  def toSet[TT >: T]: Set[TT] = this match {
    case None => Set[TT]()
    case Some(x) => Set(x)
  }
}

@library
case class Some[+T](v: T) extends Option[T]

@library
case object None extends Option[Nothing]

@library
object Option {
  @library @extern @pure
  def apply[A](x: A): Option[A] = {
    if (x == null) None else Some[A](x)
  } ensuring { res =>
    res == None || res == Some[A](x)
  }
}
