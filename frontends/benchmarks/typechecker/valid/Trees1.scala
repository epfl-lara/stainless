/* Copyright 2009-2018 EPFL, Lausanne */

import stainless.lang._

object Trees1 {
  sealed abstract class Tree[T]
  case class Node[T](left: Tree[T], right: Tree[T]) extends Tree[T]
  case class Leaf[T](value: T) extends Tree[T]

  def map[T,U](tree: Tree[T], f: T => U): Tree[U] = {
    decreases(tree)
    tree match {
      case Node(left, right) => Node(map(left, f), map(right, f))
      case Leaf(value) => Leaf(f(value))
    }
  }

  def associative_lemma[T,U,V](tree: Tree[T], f: T => U, g: U => V): Boolean = {
    map(map(tree, f), g) == map(tree, (x: T) => g(f(x)))
  }

  def associative_lemma_induct[T,U,V](tree: Tree[T], f: T => U, g: U => V): Boolean = {
    decreases(tree)
    tree match {
      case Node(left, right) => associative_lemma_induct(left, f, g) && associative_lemma_induct(right, f, g) && associative_lemma(tree, f, g)
      case Leaf(value) => associative_lemma(tree, f, g)
    }
  }.holds
}
