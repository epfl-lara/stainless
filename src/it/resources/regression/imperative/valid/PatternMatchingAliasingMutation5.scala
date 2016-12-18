object PatternMatchingAliasingMutation5 {

  case class A(var x: Int)

  abstract class List
  case class Cons(a: A, tail: List) extends List
  case class Nil() extends List

  def rec(l: List, i: BigInt): Unit = {
    require(allZero(l) && i >= 0)
    l match {
      case Cons(a, as) => 
        if(i % 2 == 0)
          a.x = 1
        rec(as, i + 1)
      case Nil() =>
        ()
    }
  } ensuring(_ => allZeroOrOne(l))

  def allZeroOrOne(l: List): Boolean = l match {
    case Cons(a, tail) => (a.x == 0 || a.x == 1) && allZeroOrOne(tail)
    case Nil() => true
  }

  def allZero(l: List): Boolean = l match {
    case Cons(a, tail) => a.x == 0 && allZero(tail)
    case Nil() => true
  }
      
}
