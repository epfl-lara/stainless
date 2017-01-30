/* Copyright 2009-2016 EPFL, Lausanne */

import stainless.annotation._
import stainless.lang._

object QuickSort {
  sealed abstract class List
  case class Cons(head:Int,tail:List) extends List
  case class Nil() extends List

  def contents(l: List): Set[Int] = l match {
    case Nil() => Set.empty
    case Cons(x,xs) => contents(xs) ++ Set(x)
  }

  def is_sorted(l: List): Boolean = l match {
    case Nil() => true
    case Cons(x,Nil()) => true
    case Cons(x,Cons(y,xs)) => x<=y && is_sorted(Cons(y,xs))
  }

  def rev_append(aList:List,bList:List): List = aList match {
    case Nil() => bList
    case Cons(x,xs) => rev_append(xs,Cons(x,bList))
  }

  def reverse(list:List): List = rev_append(list,Nil())

  def append(aList:List,bList:List): List = aList match {
    case Nil() => bList
    case _ => rev_append(reverse(aList),bList)
  }

  def greater(n:Int,list:List) : List = list match {
    case Nil() => Nil()
    case Cons(x,xs) => if (n < x) Cons(x,greater(n,xs)) else greater(n,xs)
  }

  def smaller(n:Int,list:List) : List = list match {
    case Nil() => Nil()
    case Cons(x,xs) => if (n>x) Cons(x,smaller(n,xs)) else smaller(n,xs)
  }

  def equals(n:Int,list:List) : List = list match {
    case Nil() => Nil()
    case Cons(x,xs) => if (n==x) Cons(x,equals(n,xs)) else equals(n,xs)
  }

  def quickSort(list:List): List = (list match {
    case Nil() => Nil()
    case Cons(x,Nil()) => list
    case Cons(x,xs) => append(append(quickSort(smaller(x,xs)),Cons(x,equals(x,xs))),quickSort(greater(x,xs)))
  }) ensuring(res => contents(res) == contents(list)) // && is_sorted(res))

  @ignore
  def main(args: Array[String]): Unit = {
    val ls: List = Cons(5, Cons(2, Cons(4, Cons(5, Cons(1, Cons(8,Nil()))))))

    println(ls)
    println(quickSort(ls))
  }
}
