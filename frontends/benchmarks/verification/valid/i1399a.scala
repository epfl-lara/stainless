import stainless.lang._
import stainless.collection._
import stainless.annotation._

object i1399a {

  def bar(l: List[(BigInt, Option[BigInt])]): List[Option[BigInt]] = {
    l.map{ case (left, right) => None[BigInt]()}
  }

  def barEqualsItsBody1(l: List[(BigInt, Option[BigInt])]): Unit = {
  }.ensuring(bar(l) == (l.map{ case (left, right) => None[BigInt]()}))

  def barEqualsItsBody2(l: List[(BigInt, Option[BigInt])]): Unit = {

    val a = bar(l)
    val b = l.map{ case (left, right) => None[BigInt]()}


    l match {
      case Nil() => assert(a == b)
      case Cons((key, keyMapping), t) => assert(a == b)
    }

    assert(a == b)
  }.ensuring(bar(l) == (l.map{ case (left, right) => None[BigInt]()}))


}