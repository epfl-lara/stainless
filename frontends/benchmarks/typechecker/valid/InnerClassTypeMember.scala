import stainless.lang._
import stainless.annotation._

object InnerClassTypeMember {

  abstract class Nat {
    type Repr

    def zero: Repr
    def one: Repr
    def two: Repr

    def succ(n: Repr): Repr
    def pred(n: Repr): Repr

    def toBigInt(n: Repr): BigInt
  }

  def test1 = {
    val bigIntNat: Nat = new Nat {
      type Repr = BigInt
      def zero: BigInt = 0
      def one: BigInt = 1
      def two: BigInt = 2
      def pred(n: BigInt): BigInt = if (n <= 0) 0 else n - 1
      def succ(n: BigInt): BigInt = n + 1
      def toBigInt(n: BigInt): BigInt = n
    }

    assert(bigIntNat.succ(bigIntNat.one) == bigIntNat.two)
  }

  sealed abstract class N
  case object Z extends N
  case class S(n: N) extends N

  def test2 = {
    val nNat: Nat = new Nat {
      type Repr = N
      def zero = Z
      def one = S(Z)
      def two = S(S(Z))
      def pred(n: N): N = n match {
        case Z => Z
        case S(p) => p
      }
      def succ(n: N): N = S(n)
      def toBigInt(n: N): BigInt = {
        decreases(n)
        n match {
          case Z => 0
          case S(m) => 1 + toBigInt(m)
        }
      }
    }

    assert(nNat.succ(nNat.one) == nNat.two)
  }
}


