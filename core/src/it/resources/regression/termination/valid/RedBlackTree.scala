/* Copyright 2009-2016 EPFL, Lausanne */

import stainless.lang._

object RedBlackTree { 
  sealed abstract class Color
  case class Red() extends Color
  case class Black() extends Color
 
  sealed abstract class Tree
  case class Empty() extends Tree
  case class Node(color: Color, left: Tree, value: Int, right: Tree) extends Tree

  def content(t : Tree) : Set[Int] = t match {
    case Empty() => Set.empty
    case Node(_, l, v, r) => content(l) ++ Set(v) ++ content(r)
  }

  def size(t : Tree) : Int = t match {
    case Empty() => 0
    case Node(_, l, v, r) => size(l) + 1 + size(r)
  }

  def ins(x : Int, t: Tree): Tree = (t match {
    case Empty() => Node(Red(),Empty(),x,Empty())
    case Node(c,a,y,b) =>
      if      (x < y)  balance(c, ins(x, a), y, b)
      else if (x == y) Node(c,a,y,b)
      else             balance(c,a,y,ins(x, b))
  }) ensuring (res => (
             (content(res) == content(t) ++ Set(x))
          && (size(t) <= size(res) && size(res) < size(t) + 2)
              ))

  def add(x: Int, t: Tree): Tree = {
    makeBlack(ins(x, t))
  } ensuring (content(_) == content(t) ++ Set(x))
  
  def balance(c: Color, a: Tree, x: Int, b: Tree): Tree = (Node(c,a,x,b) match {
    case Node(Black(),Node(Red(),Node(Red(),a,xV,b),yV,c),zV,d) => 
      Node(Red(),Node(Black(),a,xV,b),yV,Node(Black(),c,zV,d))
    case Node(Black(),Node(Red(),a,xV,Node(Red(),b,yV,c)),zV,d) => 
      Node(Red(),Node(Black(),a,xV,b),yV,Node(Black(),c,zV,d))
    case Node(Black(),a,xV,Node(Red(),Node(Red(),b,yV,c),zV,d)) => 
      Node(Red(),Node(Black(),a,xV,b),yV,Node(Black(),c,zV,d))
    case Node(Black(),a,xV,Node(Red(),b,yV,Node(Red(),c,zV,d))) => 
      Node(Red(),Node(Black(),a,xV,b),yV,Node(Black(),c,zV,d))
    case Node(c,a,xV,b) => Node(c,a,xV,b)
  }) ensuring (res => content(res) == content(Node(c,a,x,b)))

  def makeBlack(n: Tree): Tree = n match {
    case Node(Red(),l,v,r) => Node(Black(),l,v,r)
    case _ => n
  }

  def flip(t : Tree) : Tree = t match {
    case Empty() => Empty()
    case Node(color,l,e,r) => Node(color,flip(r),e,flip(l))
  }
}
