/* Copyright 2009-2022 EPFL, Lausanne */

package stainless
package collection

import scala.annotation.tailrec
import lang._
import annotation._
import StaticChecks._

@library
object ListOps {
  @isabelle.function(term = "List.concat")
  def flatten[T](ls: List[List[T]]): List[T] = ls match {
    case Cons(h, t) => h ++ flatten(t)
    case Nil() => Nil()
  }

  @tailrec
  def isSorted(ls: List[BigInt]): Boolean = ls match {
    case Nil() => true
    case Cons(_, Nil()) => true
    case Cons(h1, Cons(h2, _)) if(h1 > h2) => false
    case Cons(_, t) => isSorted(t)
  }

  def sorted(ls: List[BigInt]): List[BigInt] = { ls match {
    case Cons(h, t) => sortedIns(sorted(t), h)
    case Nil() => Nil[BigInt]()
  }} ensuring(isSorted(_))

  private def sortedIns(ls: List[BigInt], v: BigInt): List[BigInt] = {
    require(isSorted(ls))
    ls match {
      case Nil() => Cons(v, Nil())
      case Cons(h, t) =>
        if (v <= h) {
          Cons(v, ls)
        } else {
          Cons(h, sortedIns(t, v))
        }
    }
  } ensuring { res => isSorted(res) && res.content == ls.content + v }

  def sum(l: List[BigInt]): BigInt = l.foldLeft(BigInt(0))(_ + _)

  @tailrec
  def noDuplicate[T](l: List[T]): Boolean = l match {
    case Nil() => true
    case Cons(h, t) => !t.contains(h) && noDuplicate(t)
  }

  @library
  implicit class ListBigIntOps(l: List[BigInt]) {
    def sum: BigInt = ListOps.sum(l)

    def sorted: List[BigInt] = ListOps.sorted(l)

    def isSorted: Boolean = ListOps.isSorted(l)
  }

  @library
  implicit class FlattenableListOps[A](l: List[List[A]]) {
    def flatten: List[A] = ListOps.flatten(l)
  }

}