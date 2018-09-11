/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.lang

import stainless.annotation._

@library
sealed abstract class Option[T] {

  def get : T = {
    require(this.isDefined)
    (this : @unchecked) match {
      case Some(x) => x
    }
  }

  def getOrElse(default: =>T) = this match {
    case Some(v) => v
    case None()  => default
  }

  def orElse(or: => Option[T]) = { this match {
    case Some(v) => this
    case None() => or
  }} ensuring {
    _.isDefined == this.isDefined || or.isDefined
  }

  def isEmpty = this == None[T]()

  def nonEmpty  = !isEmpty

  def isDefined = !isEmpty


  // Higher-order API
  def map[R](f: T => R) = { this match {
    case None() => None[R]()
    case Some(x) => Some(f(x))
  }} ensuring { _.isDefined == this.isDefined }

  def flatMap[R](f: T => Option[R]) = this match {
    case None() => None[R]()
    case Some(x) => f(x)
  }

  def filter(p: T => Boolean) = this match {
    case Some(x) if p(x) => Some(x)
    case _ => None[T]()
  }

  def withFilter(p: T => Boolean) = filter(p)

  def forall(p: T => Boolean) = this match {
    case Some(x) if !p(x) => false 
    case _ => true
  }

  def exists(p: T => Boolean) = !forall(!p(_))

  /*
  // Transformation to other collections
  def toList: List[T] = this match {
    case None() => Nil[T]()
    case Some(x) => List(x)
  }
  */
  
  def toSet: Set[T] = this match {
    case None() => Set[T]()
    case Some(x) => Set(x)
  }
}

case class Some[T](v: T) extends Option[T]

case class None[T]() extends Option[T]
