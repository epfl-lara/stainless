/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package utils

sealed abstract class Perhaps[+A] {
  import Perhaps._

  def map[B](f: A => B): Perhaps[B] = this match {
    case Yes(a) => Yes(f(a))
    case _ => this.asInstanceOf[Perhaps[B]]
  }

  def flatMap[B](f: A => Perhaps[B]): Perhaps[B] = this match {
    case Yes(a) => f(a)
    case _ => this.asInstanceOf[Perhaps[B]]
  }

  def isYes: Boolean = this match {
    case Yes(_) => true
    case _ => false
  }

  def isNo: Boolean = this == No

  def isMaybe: Boolean = this == Maybe

  def isKnown: Boolean = !isMaybe

  def toOption: Option[A] = this match {
    case Yes(a) => Some(a)
    case _ => None
  }
}

object Perhaps {

  def apply[A](x: A): Perhaps[A] = {
    if (x eq null) No else Yes(x)
  }

  def fromOption[A](opt: Option[A]): Perhaps[A] = {
    opt.map(Yes(_)).getOrElse(No)
  }

  final case class Yes[A](value: A) extends Perhaps[A]
  final case object Maybe extends Perhaps[Nothing]
  final case object No extends Perhaps[Nothing]

}
