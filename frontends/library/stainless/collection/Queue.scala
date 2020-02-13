/* Copyright 2009-2019 EPFL, Lausanne */
package stainless.collection

import stainless.lang._
import stainless.annotation._
import stainless.proof._
import stainless.lang.StaticChecks._

@library
case class Queue[A](front: List[A], rear: List[A]) {
  import Queue._

  def asList: List[A] = front ++ rear.reverse

  def isAmortized: Boolean = front.size >= rear.size

  def isEmpty: Boolean = front.isEmpty && rear.isEmpty

  def tail: Queue[A] = {
    require(isAmortized && !isEmpty)
    amortizedQueue(front.tail, rear)
  } ensuring (_.isAmortized)

  def enqueue(elem: A): Queue[A] = {
    amortizedQueue(front, Cons(elem, rear))
  } ensuring(_.isAmortized)

  def head: A = {
    require(isAmortized && !isEmpty)
    front.head
  }
}

@library
object Queue {
  def empty[A]: Queue[A] = {
    Queue[A](Nil(), Nil())
  } ensuring (_.isEmpty)

  private[collection]
  def amortizedQueue[A](front: List[A], rear: List[A]): Queue[A] = {
    if (rear.size <= front.size)
      Queue(front, rear)
    else
      Queue(front ++ rear.reverse, Nil[A]())
  } ensuring (_.isAmortized)
}

@library
object QueueSpecs {
  import ListSpecs._

  def propEnqueue[A](queue: Queue[A], elem: A) : Boolean = {
    import Queue._

    val (front, rear) = (queue.front, queue.rear)

    (queue.enqueue(elem).asList == queue.asList ++ Cons(elem, Nil[A]())) because {
      assert(queue.enqueue(elem) == amortizedQueue(front, Cons(elem, rear)))

      if (Cons(elem, rear).size <= front.size) {
        assert(amortizedQueue(front, Cons(elem, rear)) == Queue(front, Cons(elem, rear)))
        assert(Queue(front, Cons(elem, rear)).asList == front ++ Cons(elem, rear).reverse)
        assert(front ++ Cons(elem, rear).reverse == front ++ (rear.reverse ++ Cons(elem, Nil[A]())))
        assert(appendAssoc(front, rear.reverse, Cons(elem, Nil[A]())))
        assert(front ++ (rear.reverse ++ Cons(elem, Nil[A]())) == (front ++ rear.reverse) ++ Cons(elem, Nil[A]()))
        assert((front ++ rear.reverse) ++ Cons(elem, Nil[A]()) == queue.asList ++ Cons(elem, Nil[A]()))

        check(queue.enqueue(elem).asList == queue.asList ++ Cons(elem, Nil[A]()))
      } else {
        assert(amortizedQueue(front, Cons(elem, rear)) == Queue(front ++ Cons(elem, rear).reverse, Nil[A]()))
        assert(Queue(front ++ Cons(elem, rear).reverse, Nil[A]()).asList == front ++ Cons(elem, rear).reverse ++ Nil[A]().reverse)
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

  def propFront[A](queue: Queue[A], elem: A) : Boolean = {
    require(!queue.isEmpty && queue.isAmortized)
    decreases(queue)

    queue.asList.head == queue.head
  }.holds

  def propTail[A](queue: Queue[A], elem: A) : Boolean = {
    require(!queue.isEmpty && queue.isAmortized)

    check(rightUnitAppend(queue.front.tail ++ queue.rear.reverse))

    queue.asList.tail == queue.tail.asList
  }.holds

  def enqueueAndFront[A](queue: Queue[A], elem: A) : Boolean = {
    if (queue.isEmpty)
      queue.enqueue(elem).head == elem
    else
      true
  }.holds

  def enqueueDequeueThrice[A](queue: Queue[A], e1: A, e2: A, e3: A): Boolean = {
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
