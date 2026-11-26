import stainless.annotation.*
import stainless.collection.*
import stainless.lang.*

object Example:
  def sum(xs: List[BigInt]): BigInt = {
    require(xs.forall(_ >= 0))
    xs match
      case Nil() => BigInt(0)
      case Cons(h, t) => h + sum(t)
  }.ensuring(_ >= 0)

  // Appending lists adds up their sums: proved by induction, using the definition of `++` that
  // Stainless extracts from the binary of its library.
  def sumAppend(xs: List[BigInt], ys: List[BigInt]): Unit = {
    require(xs.forall(_ >= 0) && ys.forall(_ >= 0))
    xs match
      case Nil() => ()
      case Cons(_, t) => sumAppend(t, ys)
  }.ensuring(_ => (xs ++ ys).forall(_ >= 0) && sum(xs ++ ys) == sum(xs) + sum(ys))

  // Not verified, as it prints
  @extern
  def main(args: Array[String]): Unit =
    println(sum(List[BigInt](1, 2, 3) ++ List[BigInt](4, 5)))
