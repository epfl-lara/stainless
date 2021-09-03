import stainless.lang._
import stainless.collection._
import stainless.lang.Option._
import stainless.annotation._
import stainless.collection.List._
import stainless.proof._

object Queue {
  final case class Node(val value: BigInt, var nextOpt: Option[Node]) extends AnyHeapRef

  def inv(asList: List[Node], i: BigInt): Boolean = {
    require(0 <= i && i <= asList.size - 1)
    reads(asList.content.asRefs)
    decreases(asList.size - 1 - i)
    
    i == asList.size - 1 ||
    {
      applyContent(asList, i);
      asList(i).nextOpt == Some(asList(i + 1)) &&
      inv(asList, i + 1)
    }
  }

  def invTail(asList: List[Node], i: BigInt): Unit = {
    require(0 <= i && i <= asList.size - 2 && inv(asList, i))
    reads(asList.content.asRefs)
    decreases(asList.size - 1 - i)

    check(inv(asList, i + 1))
    tailIndex(asList, i)
    if (i < asList.size - 2) invTail(asList, i + 1) else ()
  } ensuring(_ => inv(asList.tail, i))

  def invAgain(h0: Heap, oldAsList: List[Node], oldLast: Node, newNode: Node, i: BigInt): Unit = {
    reads((oldAsList.content ++ Set(newNode)).asRefs)
    require(0 <= i && i <= oldAsList.size - 1 &&
            h0.eval(inv(oldAsList, i)) &&            
            oldAsList.content.contains(oldLast) &&
            oldLast == oldAsList(oldAsList.size - 1) &&
            oldLast.nextOpt == Some(newNode) &&
            Heap.unchanged((oldAsList.content -- Set(oldLast)).asRefs, h0, Heap.get))
    decreases(oldAsList.size - 1 - i)

    if (i == oldAsList.size - 1) {
      val asList = oldAsList :+ newNode
      snocIndex(oldAsList, newNode, oldAsList.size)
      applyContent(asList, i)
      snocIndex(oldAsList, newNode, oldAsList.size - 1)
      check(asList(i) == oldLast)
      applyContent(asList, i + 1)
      check(asList(i).nextOpt == Some(asList(i + 1)))
      check(inv(asList, i))
    } else {
      assert(false, "Recursive case")
      check(false)
      invAgain(h0, oldAsList, oldLast, newNode, i+1)
    }
  } ensuring (_ => inv(oldAsList :+ newNode, i))
  
  final case class Q(var first: Node,
                     var last: Node,
                     var asList: List[Node])
             extends AnyHeapRef
  {
    // first node is not used to store data, it's only a sentinel

    @inlineOnce
    def valid: Boolean = {
      reads(asList.content.asRefs ++ Set(this))
      !asList.content.asRefs.contains(this) &&
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
      reads(asList.content.asRefs ++ Set(this, n))
      modifies(Set(this, last, n))

      val h0: Heap = Heap.get
      assert(h0.eval(valid))
      n.nextOpt = None[Node]()
      assert(last.nextOpt == None[Node]())
      val oldLast = last
      oldLast.nextOpt = Some(n) // the only modification of nextOpt in this method
      last = n
      val oldAsList = asList
      asList = oldAsList :+ n
      snocIndex(oldAsList, n, oldAsList.size) 
      applyContent(asList, asList.size - 1)
      snocNoDuplicate(oldAsList, n)
      check(ListOps.noDuplicate(asList))

      invAgain(h0, oldAsList, oldLast, n, 0)
    } ensuring (_ => asList == old(asList) :+ n && valid)

    def peek: Node = {
      require(asList.size >= 2 && valid)
      reads(asList.content.asRefs ++ Set(this))
      first.nextOpt match {
        case Some(nn) => nn
      }
    } ensuring ((res:Node) => res == asList(1))
  
    def dequeue: Node = {
      require(asList.size >= 2 && valid)
      reads(asList.content.asRefs ++ Set(this))
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
