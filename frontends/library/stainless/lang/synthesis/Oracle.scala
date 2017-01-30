/* Copyright 2009-2016 EPFL, Lausanne */

package stainless.lang.synthesis

import stainless.annotation._
import stainless.lang._

import scala.annotation._

@implicitNotFound("No Oracle available for this source of non-determinism, please provide an implicit arg <: Oracle[T]")
@ignore
@library
abstract class Oracle[T] {
  def head: T = this match {
    case Node(_, h, _) => h
    case Leaf(h) => h
  }

  def left: Oracle[T] = this match {
    case Node(l, _, _) => l
    case Leaf(_) => this
  }

  def right: Oracle[T] = this match {
    case Node(_, _, r) => r
    case Leaf(_) => this
  }
}

@ignore
case class Node[T](l: Oracle[T], v: T, r: Oracle[T]) extends Oracle[T];
@ignore
case class Leaf[T](v: T) extends Oracle[T];
