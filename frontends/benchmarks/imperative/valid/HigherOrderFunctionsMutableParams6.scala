object HigherOrderFunctionsMutableParams6 {

  abstract class List
  case class Cons(head: BigInt, tail: List) extends List
  case class Nil() extends List

  case class A(var x: BigInt)

  def map(ls: List, f: (BigInt, A) => BigInt, a: A): List = ls match {
    case Cons(head, tail) => 
      Cons(f(head, a), map(tail, f, a))

    case Nil() => Nil()
  }

  def fImpl(el: BigInt, a: A): BigInt = {
    val last = a.x
    a.x = el
    last
  }
  
  def shift(ls: List): List = {
    val a = A(0)
    map(ls, fImpl, a)
  }

  def test(): List = {
    val l = Cons(2, Cons(4, Cons(6, Nil())))
    shift(l)
  } ensuring(res => res == Cons(0, Cons(2, Cons(4, Nil()))))
}
