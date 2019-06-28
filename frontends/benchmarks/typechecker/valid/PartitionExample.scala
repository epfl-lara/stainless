import stainless.lang._
import stainless.annotation._

object PartitionExample {
  sealed abstract class IList
  case object Nil extends IList
  case class Cons(head: BigInt, tail: IList) extends IList

  def filter(l: IList, p: BigInt => Boolean): IList = {
    decreases(l)
    l match {
      case Nil => Nil
      case Cons(h, t) if p(h) => Cons(h, filter(t, p))
      case Cons(_, t) => filter(t, p)
    }
  }

  def partition(l: IList, p: BigInt => Boolean): (IList, IList) = {
    decreases(l)
    l match {
      case Nil => (Nil, Nil)
      case Cons(h, t) =>
        val (l1, l2) = partition(t, p)
        if (p(h)) (Cons(h, l1), l2)
        else      (l1, Cons(h, l2))
    }
  } ensuring { res =>
    res._1 == filter(l, p) &&
    res._2 == filter(l, (x: BigInt) => !p(x))
  }

  def count(l: IList, x: BigInt): BigInt = {
    decreases(l)
    l match {
      case Nil => BigInt(0)
      case Cons(h, t) => (if (h == x) BigInt(1) else BigInt(0)) + count(t, x)
    }
  }

  def partitionMultiplicity(@induct l: IList, p: BigInt => Boolean, x: BigInt): Boolean = {
    val (l1, l2) = partition(l, p)
    count(l, x) == count(l1, x) + count(l2, x)
  } holds
}

