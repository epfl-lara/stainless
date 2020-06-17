import stainless.lang._
import stainless.collection._
import stainless.annotation._
import stainless.proof._

object Filter {

  def filter1(p: BigInt => Boolean, l: List[BigInt], n: BigInt): List[BigInt] = { 
    require(l.size <= n)
    if(l.isEmpty) Nil()
    else if(p(l.head)) l.head::filter1(p, l.tail, n)
    else filter1(p, l.tail, n)
  }
  
  def filter2(p: BigInt => Boolean, l: List[BigInt], n: BigInt): List[BigInt] = {
    require(l.size <= n)
    l.filter(p)
  }
  
  @traceInduct("")
  def filter_check(p: BigInt => Boolean, l: List[BigInt], n: BigInt): Boolean = {
    require(l.size <= n)
    filter1(p, l, n) == filter2(p, l, n)
  }.holds
}
