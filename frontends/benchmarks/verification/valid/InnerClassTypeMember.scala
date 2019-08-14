
object InnerClassTypeMember {

  abstract class Nat {
    type Repr
    def zero: Repr
    def one: Repr
    def two: Repr
    def pred(n: Repr): Repr
    def succ(n: Repr): Repr
  }

  def twice(nat: Nat)(n: nat.Repr): nat.Repr = {
    var r = n
    var m = n
    while (m != nat.zero) {
      r = nat.succ(r)
      m = nat.pred(m)
    }
    r
  }

  def test1 = {
    val intNat: Nat = new Nat {
      type Repr = Int
      def zero = 0
      def one = 1
      def two = 2
      def pred(n: Int): Int = if (n <= 0) 0 else n - 1
      def succ(n: Int): Int = n + 1
    }

    assert(twice(intNat)(intNat.one) == intNat.two)
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
    }

    assert(twice(nNat)(nNat.one) == nNat.two)
  }
}
