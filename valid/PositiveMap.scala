import leon.lang._

object PositiveMap {
  
  abstract class List
  case class Cons(head: BigInt, tail: List) extends List
  case class Nil() extends List

  def positive(list: List): Boolean = list match {
    case Cons(head, tail) => if (head < 0) false else positive(tail)
    case Nil() => true
  }

  def positiveMap_passing_1(f: (BigInt) => BigInt, list: List): List = {
    list match {
      case Cons(head, tail) =>
        val fh = f(head)
        val nh = if (fh <= 0) -fh else fh
        Cons(nh, positiveMap_passing_1(f, tail))
      case Nil() => Nil()
    }
  } ensuring { res => positive(res) }

  def positiveMap_passing_2(f: (BigInt) => BigInt, list: List): List = {
    list match {
      case Cons(head, tail) =>
        val fh = f(head)
        val nh = if (fh < 0) -fh else fh
        Cons(nh, positiveMap_passing_2(f, tail))
      case Nil() => Nil()
    }
  } ensuring { res => positive(res) }

}

// vim: set ts=4 sw=4 et:
