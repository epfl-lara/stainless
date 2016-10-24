import leon.lang._

object ADTInvariants3 {

  sealed abstract class A
  sealed abstract class B extends A {
    require(this match {
      case Cons(h, t) => h == size
      case Nil(_) => true
    })

    def size: BigInt = (this match {
      case Cons(h, t) => 1 + t.size
      case Nil(_) => BigInt(0)
    }) ensuring ((i: BigInt) => i >= 0)
  }

  case class Cons(head: BigInt, tail: B) extends B
  case class Nil(i: BigInt) extends B {
    require(i >= 0)
  }

  def sum(a: A): BigInt = (a match {
    case Cons(head, tail) => head + sum(tail)
    case Nil(i) => i
  }) ensuring ((i: BigInt) => i >= 0)
}
