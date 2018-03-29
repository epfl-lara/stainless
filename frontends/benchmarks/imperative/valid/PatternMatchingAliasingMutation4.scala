object PatternMatchingAliasingMutation4 {

  case class A(var x: Int)

  sealed abstract class List
  case class Cons(a: A, tail: List) extends List
  case class Nil() extends List

  def rec(l: List): Unit = (l match {
    case Cons(a, as) => 
      a.x = 0
      rec(as)
    case Nil() =>
      ()
  }) ensuring(_ => allZero(l))

  def allZero(l: List): Boolean = l match {
    case Cons(a, tail) => a.x == 0 && allZero(tail)
    case Nil() => true
  }

  def test(): List = {
    val l = Cons(A(2), Cons(A(1), Cons(A(0), Nil())))
    rec(l)
    l
  } ensuring(l => allZero(l))

}
