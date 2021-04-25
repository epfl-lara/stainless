import stainless.lang._
import stainless.annotation._
import stainless.collection._
import stainless.proof._

object Monotonicity {

  def contains(l: List[BigInt], set: Set[BigInt], set1: Set[BigInt]): Boolean = {
    l match {
      case Cons(x, xs) => set.contains(x) && contains(xs, set, set1)
      case Nil() => true
    }    
  }
  
  @traceInduct("")
  def monotonicity(l: List[BigInt], set1: Set[BigInt], set2: Set[BigInt]): Boolean = {
    (contains(l, set1, set2) && set1.subsetOf(set2)) ==> contains(l, set2, set1)
  }.holds
}

