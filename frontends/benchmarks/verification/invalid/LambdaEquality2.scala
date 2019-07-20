import stainless.lang._
import stainless.annotation._

object LambdaEquality2 {
  sealed abstract class Nat
  case class Zero() extends Nat
  case class Succ(n: Nat) extends Nat

  def plus(a: Nat, b: Nat): Nat = a match {
    case Zero() => b
    case Succ(a2) => Succ(plus(a2,b))
  }

  @induct
  def plusZero(a: Nat) = {
    plus(a, Zero()) == a
  }.holds

  @ghost
  def equalFunctions[X,Y](y1: Y, y2: Y) = {
    require(y1 == y2)

    val f1 = (x: X) => y1
    val f2 = (x: X) => y2

    f1 == f2
  }.holds

  @ghost
  def theorem(a: Nat) = {
    val p = plus(a, Zero())
    val f1 = (x: Nat) => a
    val f2 = (x: Nat) => p
    assert(f1 != f2)
    assert(plusZero(a))
    assert(equalFunctions[Nat, Nat](a, p))
    assert(f1 == f2)
    assert(false)
  }
}
