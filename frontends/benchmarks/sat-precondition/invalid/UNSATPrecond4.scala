import stainless.collection._

object SATPrecond4 {

  def f(l: List[BigInt], x: BigInt): BigInt = {
    require(l.forall(y => y > 0))
    require(l.contains(x))
    require({
      ListSpecs.forallContained(l, y => y > 0, x)
      x < 0})
    x
 }.ensuring(res => res > 0)
}
