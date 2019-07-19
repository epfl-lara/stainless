import stainless.lang._ // for the holds keyword
import scala.language.postfixOps // to avoid warnings about postfix holds

object Factorial {
  sealed abstract class Nat
  case object O extends Nat
  case class S(n: Nat) extends Nat

  val one = S(O)
  val two = S(one)
  val three = S(two)
  val four = S(three)
  val five = S(four)
  val six = S(five)
  val seven = S(six) 
  val eight = S(seven)
  val nine = S(eight)
  val ten = S(nine)
  val eleven = S(ten)
  val twelve = S(eleven)

  def plus(n: Nat)(m: Nat): Nat = n match {
    case O => m
    case S(n2) => S(plus(n2)(m))
  }

  def mult(n: Nat)(m: Nat): Nat = n match {
    case O => O
    case S(n2) => plus(m)(mult(n2)(m))
  }

  def factorial(n: Nat): Nat = n match {
    case O => S(O)
    case S(n2) => mult(n)(factorial(n2))
  }

  def test_factorial2() = { factorial(five) == mult(ten)(twelve) }.holds
}
