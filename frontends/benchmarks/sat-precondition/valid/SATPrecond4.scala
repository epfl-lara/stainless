import stainless.collection._

object SATPrecond4 {

  def f(l: List[BigInt], x: BigInt): BigInt = {
    require(l.forall(y => y > 0))
    require(l.contains(x))
    ListSpecs.forallContained(l, y => y > 0, x)
    x
 }.ensuring(res => res > 0)
}
