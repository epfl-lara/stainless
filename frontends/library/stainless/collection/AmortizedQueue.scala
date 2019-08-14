/* Copyright 2009-2018 EPFL, Lausanne */
package stainless.collection

import stainless.lang._
import stainless.annotation._
import stainless.proof._

sealed abstract class AmortizedQueue[A] {
  import AmortizedQueue._
	
	def asList: List[A] = this match {
		case AQueue(front, rear) => front ++ rear.reverse
  }
  
  def isAmortized: Boolean = this match {
    case AQueue(front, rear) => front.size >= rear.size
  }
  
  def isEmpty: Boolean = this match {
    case AQueue(Nil(), Nil()) => true
    case _ => false
  }

  def tail: AmortizedQueue[A] = {
    require(isAmortized && !isEmpty)
    val AQueue(Cons(f, fs), rear) = this
    amortizedQueue(fs, rear)
  } ensuring (_.isAmortized)

  def enqueue(elem: A): AmortizedQueue[A] = (this match {
    case AQueue(front, rear) => amortizedQueue(front, Cons(elem, rear))
  }) ensuring(_.isAmortized)

  def head: A = {
    require(isAmortized && !isEmpty)
    val AQueue(Cons(f, _), _) = this
    f
  }
}

case class AQueue[A](front: List[A], rear: List[A]) extends AmortizedQueue[A]

object AmortizedQueue {
  def amortizedQueue[A](front: List[A], rear: List[A]) : AmortizedQueue[A] = {
    if (rear.size <= front.size)
      AQueue(front, rear)
    else
      AQueue(front ++ rear.reverse, Nil[A]())
  } ensuring(_.isAmortized)
}

object AmortizedQueueSpecs {
  import ListSpecs._

  def propEnqueue[A](queue: AQueue[A], elem: A) : Boolean = {
    import AmortizedQueue._

    val AQueue(front, rear) = queue

    (queue.enqueue(elem).asList == queue.asList ++ Cons(elem, Nil[A]())) because {
      assert(queue.enqueue(elem) == amortizedQueue(front, Cons(elem, rear)))

      if (Cons(elem, rear).size <= front.size) {
        assert(amortizedQueue(front, Cons(elem, rear)) == AQueue(front, Cons(elem, rear)))
        assert(AQueue(front, Cons(elem, rear)).asList == front ++ Cons(elem, rear).reverse)
        assert(front ++ Cons(elem, rear).reverse == front ++ (rear.reverse ++ Cons(elem, Nil[A]())))
        assert(appendAssoc(front, rear.reverse, Cons(elem, Nil[A]())))
        assert(front ++ (rear.reverse ++ Cons(elem, Nil[A]())) == (front ++ rear.reverse) ++ Cons(elem, Nil[A]()))
        assert((front ++ rear.reverse) ++ Cons(elem, Nil[A]()) == queue.asList ++ Cons(elem, Nil[A]()))
  
        check(queue.enqueue(elem).asList == queue.asList ++ Cons(elem, Nil[A]()))
      } else {
        assert(amortizedQueue(front, Cons(elem, rear)) == AQueue(front ++ Cons(elem, rear).reverse, Nil[A]()))
        assert(AQueue(front ++ Cons(elem, rear).reverse, Nil[A]()).asList == front ++ Cons(elem, rear).reverse ++ Nil[A]().reverse)
        assert(front ++ Cons(elem, rear).reverse ++ Nil[A]().reverse == front ++ Cons(elem, rear).reverse ++ Nil[A]())
        assert(front ++ Cons(elem, rear).reverse ++ Nil[A]() == front ++ Cons(elem, rear).reverse)
        assert(front ++ Cons(elem, rear).reverse == front ++ (rear.reverse ++ Cons(elem, Nil[A]())))
        assert(appendAssoc(front, rear.reverse, Cons(elem, Nil[A]())))
        assert(front ++ (rear.reverse ++ Cons(elem, Nil[A]())) == (front ++ rear.reverse) ++ Cons(elem, Nil[A]()))
        assert((front ++ rear.reverse) ++ Cons(elem, Nil[A]()) == queue.asList ++ Cons(elem, Nil[A]()))
  
        check(queue.enqueue(elem).asList == queue.asList ++ Cons(elem, Nil[A]()))
      }
    }
  }.holds
  
  def propFront[A](queue: AmortizedQueue[A], elem: A) : Boolean = {
    require(!queue.isEmpty && queue.isAmortized)
    decreases(queue)
  
    queue.asList.head == queue.head
  }.holds
  
  def propTail[A](queue: AQueue[A], elem: A) : Boolean = {
    require(!queue.isEmpty && queue.isAmortized)
  
    val AQueue(front, rear) = queue
  
    check(rightUnitAppend(front.tail ++ rear.reverse))
  
    queue.asList.tail == queue.tail.asList
  }.holds
  
  def enqueueAndFront[A](queue: AmortizedQueue[A], elem: A) : Boolean = {
    if (queue.isEmpty)
      queue.enqueue(elem).head == elem
    else
      true
  }.holds
  
  def enqueueDequeueThrice[A](queue : AmortizedQueue[A], e1: A, e2: A, e3: A): Boolean = {
    if (queue.isEmpty) {
      val q1 = queue.enqueue(e1)
      val q2 = q1.enqueue(e2)
      val q3 = q2.enqueue(e3)
      val e1prime = q3.head
      val q4 = q3.tail
      val e2prime = q4.head
      val q5 = q4.tail
      val e3prime = q5.head
      e1 == e1prime && e2 == e2prime && e3 == e3prime
    } else
      true
  }.holds
}