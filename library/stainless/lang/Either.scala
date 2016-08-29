/* Copyright 2009-2016 EPFL, Lausanne */

package stainless.lang

import stainless.annotation._

/**
 * @author Viktor
 */
@library
sealed abstract class Either[A,B] {
  def isLeft : Boolean
  def isRight : Boolean
  def swap : Either[B,A]
}
@library
case class Left[A,B](content: A) extends Either[A,B] {
  def isLeft = true
  def isRight = false
  def swap = Right[B,A](content)
}
@library
case class Right[A,B](content: B) extends Either[A,B] {
  def isLeft = false
  def isRight = true
  def swap = Left[B,A](content)
}
