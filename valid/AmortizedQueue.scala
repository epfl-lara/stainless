import scala.collection.immutable.Set
import leon.Utils._
import leon.Annotations._

object AmortizedQueue {
  sealed abstract class List
  case class Cons(head : Int, tail : List) extends List
  case class Nil() extends List

  sealed abstract class AbsQueue
  case class Queue(front : List, rear : List) extends AbsQueue

  def size(list : List) : Int = (list match {
    case Nil() => 0
    case Cons(_, xs) => 1 + size(xs)
  }) ensuring(_ >= 0)

  def content(l: List) : Set[Int] = l match {
    case Nil() => Set.empty[Int]
    case Cons(x, xs) => Set(x) ++ content(xs)
  }
  
  def asList(queue : AbsQueue) : List = queue match {
    case Queue(front, rear) => concat(front, reverse(rear))
  }

  def concat(l1 : List, l2 : List) : List = (l1 match {
    case Nil() => l2
    case Cons(x,xs) => Cons(x, concat(xs, l2))
  }) ensuring (res => size(res) == size(l1) + size(l2) && content(res) == content(l1) ++ content(l2))

  def isAmortized(queue : AbsQueue) : Boolean = queue match {
    case Queue(front, rear) => size(front) >= size(rear)
  }

  def isEmpty(queue : AbsQueue) : Boolean = queue match {
    case Queue(Nil(), Nil()) => true
    case _ => false
  }

  def reverse(l : List) : List = (l match {
    case Nil() => Nil()
    case Cons(x, xs) => concat(reverse(xs), Cons(x, Nil()))
  }) ensuring (content(_) == content(l))

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

  // @induct
  // def propEnqueue(rear : List, front : List, list : List, elem : Int) : Boolean = {
  //   require(isAmortized(Queue(front, rear)))
  //   val queue = Queue(front, rear)
  //   if (asList(queue) == list) {
  //     asList(enqueue(queue, elem)) == concat(list, Cons(elem, Nil()))
  //   } else
  //     true
  // } holds

  @induct
  def propFront(queue : AbsQueue, list : List, elem : Int) : Boolean = {
    require(!isEmpty(queue) && isAmortized(queue))
    if (asList(queue) == list) {
      list match {
        case Cons(x, _) => front(queue) == x
      }
    } else
      true
  } holds

  @induct
  def propTail(rear : List, front : List, list : List, elem : Int) : Boolean = {
    require(!isEmpty(Queue(front, rear)) && isAmortized(Queue(front, rear)))
    if (asList(Queue(front, rear)) == list) {
      list match {
        case Cons(_, xs) => asList(tail(Queue(front, rear))) == xs
      }
    } else
      true
  } // holds

  def enqueueAndFront(queue : AbsQueue, elem : Int) : Boolean = {
    if (isEmpty(queue))
      front(enqueue(queue, elem)) == elem
    else
      true
  } holds

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
  } holds
}
