import stainless.lang._
import stainless.collection._
import stainless.annotation._
import stainless.proof._

object Sorted {

  def sorted1(l: List[BigInt]): Boolean = {
    if(l.isEmpty) true
    else if (l.size == 1) true
    else if (l.head > l.tail.head) false
    else sorted1(l.tail)
  }//ensuring(res => res == sorted2(l))

  def sorted2(l: List[BigInt]): Boolean = {
    l match {
      case Nil() => true
      case Cons(_, Nil()) => true
      case Cons(h1, Cons(h2, _)) if(h1 > h2) => false
      case Cons(_, t) => sorted2(t)
    }
  }//ensuring(res => res == sorted1(l))

  @traceInduct("")
  def sorted_check(l: List[BigInt]): Boolean = {
    sorted1(l) == sorted2(l)
  }.holds

}
