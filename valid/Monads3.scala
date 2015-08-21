/* Copyright 2009-2015 EPFL, Lausanne */

import leon.lang._
import leon.collection._

object Monads3 {

  def append[T](l1: List[T], l2: List[T]): List[T] = {
    l1 match {
      case Cons(head, tail) => Cons(head, append(tail, l2))
      case Nil() => l2
    }
  } ensuring { res => (res == l1) || (l2 != Nil[T]()) }

  def flatMap[T,U](list: List[T], f: T => List[U]): List[U] = list match {
    case Cons(head, tail) => append(f(head), flatMap(tail, f))
    case Nil() => Nil()
  }

  def associative_lemma[T,U,V](list: List[T], f: T => List[U], g: U => List[V]): Boolean = {
    flatMap(flatMap(list, f), g) == flatMap(list, (x: T) => flatMap(f(x), g))
  }

  def associative_lemma_induct[T,U,V](list: List[T], flist: List[U], glist: List[V], f: T => List[U], g: U => List[V]): Boolean = {
    associative_lemma(list, f, g) &&
    append(glist, flatMap(append(flist, flatMap(list, f)), g)) == append(append(glist, flatMap(flist, g)), flatMap(list, (x: T) => flatMap(f(x), g))) &&
    (glist match {
      case Cons(ghead, gtail) =>
        associative_lemma_induct(list, flist, gtail, f, g)
      case Nil() => flist match {
        case Cons(fhead, ftail) =>
          associative_lemma_induct(list, ftail, g(fhead), f, g)
        case Nil() => list match {
          case Cons(head, tail) => associative_lemma_induct(tail, f(head), Nil(), f, g)
          case Nil() => true
        }
      }
    })
  }.holds

  def left_unit_law[T,U](x: T, f: T => List[U]): Boolean = {
    flatMap(Cons(x, Nil()), f) == f(x)
  }.holds

  def right_unit_law[T](list: List[T]): Boolean = {
    flatMap(list, (x: T) => Cons(x, Nil())) == list
  }
    
  def right_unit_induct[T,U](list: List[T]): Boolean = {
    right_unit_law(list) && (list match {
      case Cons(head, tail) => right_unit_induct(tail)
      case Nil() => true
    })
  }.holds

  def flatMap_zero_law[T,U](f: T => List[U]): Boolean = {
    flatMap(Nil[T](), f) == Nil[U]()
  }.holds

  def flatMap_to_zero_law[T](list: List[T]): Boolean = {
    flatMap(list, (x: T) => Nil[T]()) == Nil[T]()
  }
    
  def flatMap_to_zero_induct[T,U](list: List[T]): Boolean = {
    flatMap_to_zero_law(list) && (list match {
      case Cons(head, tail) => flatMap_to_zero_induct(tail)
      case Nil() => true
    })
  }.holds

  def add_zero_law[T](list: List[T]): Boolean = {
    append(list, Nil()) == list
  }.holds

  def zero_add_law[T](list: List[T]): Boolean = {
    append(Nil(), list) == list
  }.holds

}
