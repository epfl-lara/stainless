/* Copyright 2009-2024 EPFL, Lausanne */
/* Based on https://github.com/leanprover-community/lean-auto/blob/bfd373fb8ee85a0255f64b4f376e5fb08bb8a1da/Auto/Lib/ListExtra.lean#L111-L121 */
/* TODO: investigate crash with --solvers=princess  */

import stainless.annotation.*
import stainless.collection.*
import stainless.lang.*

object LeanMergeSort {
  def isSorted(list: List[Int]): Boolean = {
    decreases(list)
    list match 
      case Cons(x1, tail @ Cons(x2, _)) => x1 <= x2 && isSorted(tail)
      case _ => true
  }

  def merge(l1: List[Int], l2: List[Int]): List[Int] = {
    require(isSorted(l1) && isSorted(l2))
    decreases(l1.length + l2.length)
    (l1, l2) match {
      case (Cons(x, xs), Cons(y, ys)) =>
        if (x <= y) Cons(x, merge(xs, l2))
        else Cons(y, merge(l1, ys))
      case _ => l1 ++ l2
    }
  }.ensuring { res =>
    isSorted(res) &&
    res.length == l1.length + l2.length &&
    res.content == l1.content ++ l2.content // sets are faster than bags
  }

  def split(list: List[Int]): (List[Int], List[Int]) = {    
    decreases(list)
    list match {
      case Cons(x1, Cons(x2, xs)) =>
        val (s1, s2) = split(xs)
        (Cons(x1, s1), Cons(x2, s2))
      case _ => (Nil[Int](), list)
    }
  }.ensuring { res =>
   res._1.size + res._2.size == list.size &&
   res._1.content ++ res._2.content == list.content
  }
  
  def leanMergeSort(list: List[Int]): List[Int] = {
    decreases(list.length)
    list match {
      case Cons(h1, Cons(h2, rest)) =>
        val (s1, s2) = split(rest)
        merge(leanMergeSort(s1), leanMergeSort(s2))
      case _ => list
    }
  }.ensuring { res => 
    isSorted(res) && res.length <= list.length &&
    res.content.subsetOf(list.content)
  }

  @main @extern
  def test1 = 
    val list = List.fromScala((1 to 21).toList)
      // Clément points out: https://dl.acm.org/doi/10.1145/3127585
    println(f"list = $list")
    val leanSorted = leanMergeSort(list)
    println(f"leanMergeSort(list) = $leanSorted")
}
