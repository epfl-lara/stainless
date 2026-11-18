import stainless.collection._
import stainless.lang._
import stainless.annotation._

object FoldLeftMut {

  def foldLeftMut[A, @mutable B](l: List[A], z: B, f: (B, A) => Unit): Unit = {
    l match {
      case Nil() => ()
      case Cons(h, t) =>
        f(z, h)
        foldLeftMut(t, z, f)
    }
  }

  case class MutableInt(var value: BigInt) {
    require(value >= 0)
  }

  type PosBigInt = {x: BigInt with x >= 0}

  def main(): Unit = {
    val l: List[PosBigInt] = List(BigInt(1), BigInt(2), BigInt(3))
    val sum: MutableInt = MutableInt(0)
    foldLeftMut(l, sum, (acc: MutableInt, x: PosBigInt) => {
      acc.value += x
    })
    assert(sum.value == 6)
  }

}
