import stainless.lang._
import stainless.collection._
import stainless.annotation._
import stainless.proof._

object Map {

  def map1(p: BigInt => BigInt, l: List[BigInt]): List[BigInt] = { 
    l.map(p)
  }

  def map2(p:BigInt => BigInt, l: List[BigInt]): List[BigInt] = {
    if(l.isEmpty) Nil()
    else p(l.head)::map2(p, l.tail)
  }

  @traceInduct("")
  def map_check(p: BigInt => BigInt, l: List[BigInt]): Boolean = {
    map1(p, l) == map2(p, l)
  }.holds
}
