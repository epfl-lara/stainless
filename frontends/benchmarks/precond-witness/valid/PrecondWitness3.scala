import stainless.lang._
import stainless.collection._

object PrecondWitness3 {
  // Several preconditions, several parameters, type parameters, and several witnesses
  def get[T](l: List[T], i: BigInt): T = {
    require(i >= 0)
    require(i < l.size)
    precondWitness(get(Cons(1, Cons(2, Nil())), 1))
    precondWitness(get[Boolean](Cons(true, Nil()), 0))
    decreases(l)
    l match {
      case Cons(h, t) => if (i == 0) h else get(t, i - 1)
    }
  }.ensuring(res => l.contains(res))

  // The witness can call other functions
  def double(x: BigInt): BigInt = 2 * x

  def half(x: BigInt): BigInt = {
    require(x >= 0 && x % 2 == 0)
    precondWitness(half(double(21)))
    x / 2
  }.ensuring(res => 2 * res == x)
}
