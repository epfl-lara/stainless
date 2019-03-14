
import stainless.lang._
import stainless.proof._
import stainless.annotation._

object NatMonoidLaws {

  sealed abstract class Nat {
    def +(m: Nat): Nat = {
      decreases(this)
      this match {
        case Zero => m
        case Succ(n) => Succ(n + m)
      }
    }

    def *(m: Nat): Nat = {
      decreases(this)
      this match {
        case Zero => Zero
        case Succ(n) => n * m + m
      }
    }
  }

  final case object Zero extends Nat
  final case class Succ(prev: Nat) extends Nat

  final val One = Succ(Zero)

  def lemma_rightIdentity_plus(@induct x: Nat): Boolean = {
    decreases(x)
    x + Zero == x
  }.holds

  def lemma_associativity_plus(@induct x: Nat, y: Nat, z: Nat): Boolean = {
    decreases(x)
    x + (y + z) == (x + y) + z
  }.holds

  abstract class NatMonoid {
    def empty: Nat
    def append(x: Nat, y: Nat): Nat

    @law
    def law_leftIdentity(x: Nat) = {
      append(empty, x) == x
    }

    @law
    def law_rightIdentity(x: Nat) = {
      append(x, empty) == x
    }

    @law
    def law_associativity(x: Nat, y: Nat, z: Nat) = {
      append(x, append(y, z)) == append(append(x, y), z)
    }
  }

  case class AdditiveMonoid() extends NatMonoid {
    def empty = Zero

    def append(x: Nat, y: Nat) = x + y

    override def law_rightIdentity(x: Nat) = {
      super.law_rightIdentity(x) because lemma_rightIdentity_plus(x)
    }

    override def law_associativity(x: Nat, y: Nat, z: Nat) = {
      super.law_associativity(x, y, z) because lemma_associativity_plus(x, y, z)
    }
  }

}
