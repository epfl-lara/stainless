/* Copyright 2009-2021 EPFL, Lausanne */

import stainless.lang._
import stainless.math._
import stainless.lang._

object BinomialHeap {
  //sealed abstract class TreeNode
  case class TreeNode(rank: BigInt, elem: Element, children: BinomialHeap)
  case class Element(n: BigInt)

  sealed abstract class BinomialHeap
  case class ConsHeap(head: TreeNode, tail: BinomialHeap) extends BinomialHeap
  case class NilHeap() extends BinomialHeap

  sealed abstract class List
  case class NodeL(head: BinomialHeap, tail: List) extends List
  case class NilL() extends List

  sealed abstract class OptionalTree
  case class Some(t : TreeNode) extends OptionalTree
  case class None() extends OptionalTree

  /* Lower or Equal than for Element structure */
  private def leq(a: Element, b: Element) : Boolean = {
    a match {
      case Element(a1) => {
        b match {
          case Element(a2) => {
            if(a1 <= a2) true
            else false
          }
        }
      }
    }
  }

  /* isEmpty function of the Binomial Heap */
  def isEmpty(t: BinomialHeap) = t match {
    case ConsHeap(_,_) => false
    case _ => true
  }

  /* Helper function to determine rank of a TreeNode */
  def rank(t: TreeNode) : BigInt = t.rank /*t match {
    case TreeNode(r, _, _) => r
  }*/

  /* Helper function to get the root element of a TreeNode */
  def root(t: TreeNode) : Element = t.elem /*t match {
    case TreeNode(_, e, _) => e
  }*/

  /* Linking trees of equal ranks depending on the root element */
  def link(t1: TreeNode, t2: TreeNode): TreeNode = {
    if (leq(t1.elem, t2.elem)) {
      TreeNode(t1.rank + 1, t1.elem, ConsHeap(t2, t1.children))
    } else {
      TreeNode(t1.rank + 1, t2.elem, ConsHeap(t1, t2.children))
    }
  }

  def treeNum(h: BinomialHeap) : BigInt = {
    h match {
      case ConsHeap(head, tail) =>  1 + treeNum(tail)
      case _ => BigInt(0)
    }
  } ensuring(_ >= 0)

  /* Insert a tree into a binomial heap. The tree should be correct in relation to the heap */
  def insTree(t: TreeNode, h: BinomialHeap) : BinomialHeap = {
    h match {
      case ConsHeap(head, tail) =>  {
        if (rank(t) < rank(head)) {
          ConsHeap(t, h)
        } else if (rank(t) > rank(head)) {
          ConsHeap(head, insTree(t,tail))
        } else {
          insTree(link(t,head), tail)
        }
      }
      case _ => ConsHeap(t, NilHeap())
    }
  } //ensuring(_ => steps <= ? * treeNum(h) + ?)

  /* Merge two heaps together */
  def merge(h1: BinomialHeap, h2: BinomialHeap): BinomialHeap = {
    decreases(treeNum(h1) + treeNum(h2))
    h1 match {
      case ConsHeap(head1, tail1) => {
        h2 match {
          case ConsHeap(head2, tail2) => {
            if (rank(head1) < rank(head2)) {
              ConsHeap(head1, merge(tail1, h2))
            } else if (rank(head2) < rank(head1)) {
              ConsHeap(head2, merge(h1, tail2))
            } else {
              mergeWithCarry(link(head1, head2), tail1, tail2)
            }
          }
          case _ => h1
        }
      }
      case _ => h2
    }
  } //ensuring(_ => steps <= ? *  + ?)

  def mergeWithCarry(t: TreeNode, h1: BinomialHeap, h2: BinomialHeap): BinomialHeap = {
    decreases(treeNum(h1) + treeNum(h2))
    h1 match {
      case ConsHeap(head1, tail1) => {
        h2 match {
          case ConsHeap(head2, tail2) => {
            if (rank(head1) < rank(head2)) {

              if (rank(t) < rank(head1))
                ConsHeap(t, ConsHeap(head1, merge(tail1, h2)))
              else
                mergeWithCarry(link(t, head1), tail1, h2)

            } else if (rank(head2) < rank(head1)) {

              if (rank(t) < rank(head2))
                ConsHeap(t, ConsHeap(head2, merge(h1, tail2)))
              else
                mergeWithCarry(link(t, head2), h1, tail2)

            } else {
              ConsHeap(t, mergeWithCarry(link(head1, head2), tail1, tail2))
            }
          }
          case _ => {
            insTree(t, h1)
          }
        }
      }
      case _ => insTree(t, h2)
    }
  } //ensuring (_ => steps <= ? * treeNum(h1) + ? * treeNum(h2) + ?)

  //Auxiliary helper function to simplefy findMin and deleteMin
  def removeMinTree(h: BinomialHeap): (OptionalTree, BinomialHeap) = {
    h match {
      case ConsHeap(head, NilHeap()) => (Some(head), NilHeap())
      case ConsHeap(head1, tail1) => {
        val (opthead2, tail2) = removeMinTree(tail1)
        opthead2 match {
          case Some(head2) =>
            if (leq(root(head1), root(head2))) {
              (Some(head1), tail1)
            } else {
              (Some(head2), ConsHeap(head1, tail2))
            }
          case _ => (Some(head1), tail1)
        }
      }
      case _ => (None(), NilHeap())
    }
  } //ensuring (res => treeNum(res._2) <= treeNum(h) && steps <= ? * treeNum(h) + ?)

  /*def findMin(h: BinomialHeap) : Element = {
    val (opt, _) = removeMinTree(h)
    opt match {
      case Some(TreeNode(_,e,ts1)) => e
      case _ => Element(-1)
    }
  } ensuring(res => true && tmpl((a,b) => steps <= a*treeNum(h) + b))*/

  def minTreeChildren(h: BinomialHeap) : BigInt = {
    val (min, _) = removeMinTree(h)
    min match {
      case Some(TreeNode(_,_,ch)) => treeNum(ch)
      case _ => 0
    }
  }

  // Discard the minimum element of the extracted min tree and put its children back into the heap
  def deleteMin(h: BinomialHeap) : BinomialHeap = {
    val (min, ts2) = removeMinTree(h)
    min match {
      case Some(TreeNode(_,_,ts1)) => merge(ts1, ts2)
      case _ => h
    }
  } //ensuring(_ => steps <= ? * minTreeChildren(h) + ? * treeNum(h) + ?)

}
