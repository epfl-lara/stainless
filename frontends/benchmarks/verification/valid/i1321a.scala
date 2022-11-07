object i1321a {
  sealed abstract class List[+A] {
    def map[B](f: A => B): List[B] = this match {
      case Nil => Nil
      case Cons(a, as) => Cons(f(a), as.map(f))
    }
  }
  case object Nil extends List[Nothing]
  case class Cons[+A](head: A, tail: List[A]) extends List[A]

  trait MyInt {
    def x: BigInt
  }

  final case class PosInt(v: BigInt) extends MyInt {
    require(0 <= v)
    def x = v
  }

  def applyTwice[A](xs: List[A], f: A => A): List[A] =
    xs.map(f).map(f)

  def getPos(n: BigInt): List[PosInt] = {
    require(0 <= n)
    if (n <= 0) Nil
    else Cons(PosInt(n), getPos(n-1))
  }

  def onlyPos(x: PosInt): PosInt =
    PosInt(x.v + 1)

  def work(n: BigInt) = {
    require(0 <= n)
    applyTwice[PosInt](getPos(n), xyz => onlyPos(xyz))
  }
}