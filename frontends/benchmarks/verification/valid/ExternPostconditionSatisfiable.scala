import stainless.lang._
import stainless.annotation._
import stainless.collection._

object ExternPostconditionSatisfiable {
  @extern def nonNegative(): BigInt = {
    (??? : BigInt)
  }.ensuring(res => res >= 0)

  @extern def above(x: BigInt): BigInt = {
    require(x >= 0)
    (??? : BigInt)
  }.ensuring(res => res > x)

  @extern def bounded(x: Int): Int = {
    (??? : Int)
  }.ensuring(res => 0 <= res && res < 10)

  @extern def ofSize(n: BigInt): List[BigInt] = {
    require(n >= 0)
    (??? : List[BigInt])
  }.ensuring(res => res.size == n)

  @extern def split(x: BigInt): (BigInt, BigInt) = {
    (??? : (BigInt, BigInt))
  }.ensuring(res => res._1 + res._2 == x)

  @extern def fill(a: Array[Int], v: Int): Unit = {
    (??? : Unit)
  }.ensuring(_ => a.length == old(a).length && (a.length == 0 || a(0) == v))

  // Without a postcondition, there is nothing to check
  @extern def anything(x: BigInt): BigInt = (??? : BigInt)

  def caller(x: BigInt): BigInt = {
    require(x >= 0)
    val y = above(x)
    val (a, b) = split(y)
    a + b
  }.ensuring(res => res > x)
}
