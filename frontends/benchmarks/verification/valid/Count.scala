import stainless.lang._
import stainless.collection._
import stainless.annotation._
import stainless.proof._

object Count {

  def count1(p: BigInt => Boolean, l: List[BigInt]): BigInt = {
    l match {
      case Nil() => BigInt(0)
      case h::t => (if (p(l.head)) BigInt(1) else BigInt(0)) + count1(p, l.tail)
    }
  }//ensuring(res => res == count2(p, l))

  def count2(p: BigInt => Boolean, l: List[BigInt]): BigInt = {
    l.filter(p).size 
  }//ensuring(res => res == count1(p, l))

  @traceInduct("")
  def count_check(p: BigInt => Boolean, l: List[BigInt]): Boolean = {
    count1(p, l) == count2(p, l)
  }.holds
}
