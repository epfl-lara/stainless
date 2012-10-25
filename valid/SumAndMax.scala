import leon.Utils._
import leon.Annotations._

object SumAndMax {
  sealed abstract class List
  case class Cons(head : Int, tail : List) extends List
  case class Nil() extends List

  def max(list : List) : Int = {
    require(list != Nil())
    list match {
      case Cons(x, Nil()) => x
      case Cons(x, xs) => {
        val m2 = max(xs)
        if(m2 > x) m2 else x
      }
    }
  }

  def sum(list : List) : Int = list match {
    case Nil() => 0
    case Cons(x, xs) => x + sum(xs)
  }

  def size(list : List) : Int = (list match {
    case Nil() => 0
    case Cons(_, xs) => 1 + size(xs)
  }) ensuring(_ >= 0)

  def allPos(list : List) : Boolean = list match {
    case Nil() => true
    case Cons(x, xs) => x >= 0 && allPos(xs)
  }

  def prop0(list : List) : Boolean = {
    require(list != Nil())
    !allPos(list) || max(list) >= 0
  } holds

  @induct
  def property(list : List) : Boolean = {
    // This precondition was given in the problem but isn't actually useful :D
    // require(allPos(list))
    sum(list) <= size(list) * (if(list == Nil()) 0 else max(list))
  } holds
}
