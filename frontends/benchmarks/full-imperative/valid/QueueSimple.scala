import stainless.lang._
import stainless.collection._
import stainless.lang.Option._
import stainless.annotation._
import stainless.collection.List._
import stainless.proof._

object Queue {
  final case class Node(val value: BigInt, var nextOpt: Option[Node]) extends AnyHeapRef

  def inv(asList: List[AnyHeapRef], i: BigInt): Boolean = {
    require(0 <= i && i <= asList.size - 1)
    reads(asList.content)
    decreases(asList.size - 1 - i)
    
    i == asList.size - 1 ||
    {
      applyContent(asList, i);
      (asList(i).isInstanceOf[Node] && asList(i).asInstanceOf[Node].nextOpt == Some(asList(i + 1)) &&
       inv(asList, i + 1))
    }
  }

  def invTail(asList: List[AnyHeapRef], i: BigInt): Unit = {
    require(0 <= i && i <= asList.size - 2 && inv(asList, i))
    reads(asList.content)
    decreases(asList.size - 1 - i)

    check(inv(asList, i + 1))
    tailIndex(asList, i)
    if (i < asList.size - 2) invTail(asList, i + 1) else ()
  } ensuring(_ => inv(asList.tail, i))
  
  final case class Q(var first: Node,
                     var last: Node,
                     var asList: List[AnyHeapRef])
             extends AnyHeapRef
  {
    // first node is not used, tis only a sentinel

    @inlineOnce
    def valid: Boolean = {
      reads(asList.content ++ Set(this))
      !asList.content.contains(this) &&
      asList.size >= 1 &&
      asList(0) == first &&      
      asList(asList.size - 1) == last &&
      asList.content.contains(last) && // follows by applyContent(asList, asList.size - 1)
      last.nextOpt == None[Node]() &&
      ListOps.noDuplicate(asList) &&
      inv(asList, 0)
    }

    def enqueue(n: Node): Unit = {
      require(!asList.content.contains(n) && n.nextOpt == None[Node] && valid)
      reads(asList.content ++ Set(this, n))
      modifies(Set(this, last, n))

      n.nextOpt = None[Node]()
      assert(last.nextOpt == None[Node]())
      last.nextOpt = Some(n) // the only modification of nextOpt in this method
      last = n
      val oldAsList = asList
      asList = oldAsList :+ n
      snocIndex(oldAsList, n, oldAsList.size) 
      applyContent(asList, asList.size - 1)
      snocNoDuplicate(oldAsList, n)
      check(ListOps.noDuplicate(asList))
      check(inv(asList, 0)) // needs induction, that inv was true, and noDuplicate
    } ensuring (_ => asList == old(asList) :+ n && valid)

    def peek: Node = {
      require(asList.size >= 2 && valid)
      reads(asList.content ++ Set(this))
      first.nextOpt match {
        case Some(nn) => nn
      }
    } ensuring ((res:Node) => res == asList(1))
  
    def dequeue: Node = {
      require(asList.size >= 2 && valid)
      reads(asList.content ++ Set(this))
      modifies(Set(this))

      first.nextOpt match {
        case Some(nn) => {
          val oldAsList = asList
          first = nn
          asList = asList.tail
          check(asList(0) == first)
          tailIndex(oldAsList, asList.size - 1)
          check(asList.size == oldAsList.size - 1)
          check(asList(asList.size - 1) == last)
          applyContent(asList, asList.size - 1)
          check(asList.content.contains(last))
          check(last.nextOpt == None[Node]())
          invTail(oldAsList, 0) // for the inv(asList, 0)
          check(inv(asList, 0)) 
          nn
        }
      }
    } ensuring ((res:Node) => 
                asList == old(asList).tail &&
                res == old(asList).apply(1) &&
                valid)
  }

  def snocLast[T](l: List[T], x: T): Unit = {
    l match {
      case Nil() => ()
      case Cons(y, ys) => snocLast(ys, x)
    }
  } ensuring(_ => (l :+ x).last == x)

  def snocIndex[T](l: List[T], t: T, i: BigInt): Unit = {
    require(0 <= i && i < l.size + 1)
    decreases(l)
    l match {
      case Nil() => ()
      case Cons(x, xs) => if (i > 0) snocIndex[T](xs, t, i-1) else ()
    }
  } ensuring(_ => ((l :+ t).apply(i) == (if (i < l.size) l(i) else t)))

  def snocNoDuplicate[T](l: List[T], t: T): Unit = {
    require(ListOps.noDuplicate(l) && !l.contains(t))
    l match {
      case Nil() => ()
      case Cons(y, ys) => snocNoDuplicate(ys, t)
    }
  } ensuring(_ => ListOps.noDuplicate(l :+ t))

  
  def tailIndex[T](l: List[T], i: BigInt): Unit = {
    require(0 < l.size && 0 <= i && i < l.size - 1)
    decreases(l)
    l match {
      case Cons(x, xs) => if (i > 0) tailIndex[T](xs, i-1) else ()
    }
  } ensuring(_ => l.tail(i) == l(i + 1))
  
  def applyContent[T](list: List[T], index: BigInt): Unit = {
    require(0 <= index && index < list.size)
    list match {
      case Cons(_, xs) => if (index > 0) applyContent[T](xs, index-1) else ()
    }
  } ensuring(_ => list.content.contains(list.apply(index)))
}
