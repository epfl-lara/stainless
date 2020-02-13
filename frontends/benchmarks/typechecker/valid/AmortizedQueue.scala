/* Copyright 2009-2019 EPFL, Lausanne */

import stainless.lang._
import stainless.annotation._
import stainless.proof._

object AmortizedQueue {
  sealed abstract class List
  case class Cons(head : Int, tail : List) extends List
  case class Nil() extends List

  sealed abstract class AbsQueue
  case class Queue(front : List, rear : List) extends AbsQueue

  def head(list: List): Int = {
    require(list != Nil())

    val Cons(res, _) = list
    res
  }

  def tail(list: List): List = {
    require(list != Nil())

    val Cons(_, res) = list
    res
  }

  def size(list : List) : BigInt = {
    decreases(list)
    list match {
      case Nil() => BigInt(0)
      case Cons(_, xs) => 1 + size(xs)
    }
   } ensuring(_ >= 0)

  def content(l: List) : Set[Int] = {
    decreases(l)
    l match {
      case Nil() => Set.empty[Int]
      case Cons(x, xs) => Set(x) ++ content(xs)
    }
  }

  def asList(queue : AbsQueue) : List = queue match {
    case Queue(front, rear) => concat(front, reverse(rear))
  }

  def concat(l1 : List, l2 : List) : List = {
    decreases(l1)
    l1 match {
      case Nil() => l2
      case Cons(x,xs) => Cons(x, concat(xs, l2))
    }
  } ensuring (res => size(res) == size(l1) + size(l2) && content(res) == content(l1) ++ content(l2))

  def concatNil(@induct l: List) = {
    concat(l, Nil()) == l
  }.holds

  def concatAssoc(@induct l1: List, l2: List, l3: List) = {
    concat(l1, concat(l2, l3)) == concat(concat(l1, l2), l3)
  }.holds

  def isAmortized(queue : AbsQueue) : Boolean = queue match {
    case Queue(front, rear) => size(front) >= size(rear)
  }

  def isEmpty(queue : AbsQueue) : Boolean = queue match {
    case Queue(Nil(), Nil()) => true
    case _ => false
  }

  def reverse(l : List) : List = {
    decreases(l)
    l match {
      case Nil() => Nil()
      case Cons(x, xs) => concat(reverse(xs), Cons(x, Nil()))
    }
  } ensuring (content(_) == content(l))

  def amortizedQueue(front : List, rear : List) : AbsQueue = {
    if (size(rear) <= size(front))
      Queue(front, rear)
    else
      Queue(concat(front, reverse(rear)), Nil())
  } ensuring(isAmortized(_))

  def enqueue(queue : AbsQueue, elem : Int) : AbsQueue = (queue match {
    case Queue(front, rear) => amortizedQueue(front, Cons(elem, rear))
  }) ensuring(isAmortized(_))

  def tail(queue : AbsQueue) : AbsQueue = {
    require(isAmortized(queue) && !isEmpty(queue))
    queue match {
      case Queue(Cons(f, fs), rear) => amortizedQueue(fs, rear)
    }
  } ensuring (isAmortized(_))

  def front(queue : AbsQueue) : Int = {
    require(isAmortized(queue) && !isEmpty(queue))
    queue match {
      case Queue(Cons(f, _), _) => f
    }
  }

  def propEnqueue(queue: Queue, elem : Int) : Boolean = {
    val Queue(front, rear) = queue
    check(concatAssoc(front, reverse(rear), Cons(elem, Nil())))
    check(concatNil(concat(front, concat(reverse(rear), Cons(elem, Nil())))))

    asList(enqueue(queue, elem)) == concat(asList(queue), Cons(elem, Nil()))
  }.holds

  def propFront(queue : AbsQueue, elem : Int) : Boolean = {
    require(!isEmpty(queue) && isAmortized(queue))
    decreases(queue)

    head(asList(queue)) == front(queue)
  }.holds

  def propTail(queue: Queue, elem : Int) : Boolean = {
    require(!isEmpty(queue) && isAmortized(queue))

    val Queue(front, rear) = queue

    check(concatNil(concat(tail(front), reverse(rear))))

    tail(asList(queue)) == asList(tail(queue))
  }.holds

  def enqueueAndFront(queue : AbsQueue, elem : Int) : Boolean = {
    if (isEmpty(queue))
      front(enqueue(queue, elem)) == elem
    else
      true
  }.holds

  def enqueueDequeueThrice(queue : AbsQueue, e1 : Int, e2 : Int, e3 : Int) : Boolean = {
    if (isEmpty(queue)) {
      val q1 = enqueue(queue, e1)
      val q2 = enqueue(q1, e2)
      val q3 = enqueue(q2, e3)
      val e1prime = front(q3)
      val q4 = tail(q3)
      val e2prime = front(q4)
      val q5 = tail(q4)
      val e3prime = front(q5)
      e1 == e1prime && e2 == e2prime && e3 == e3prime
    } else
      true
  }.holds
}
