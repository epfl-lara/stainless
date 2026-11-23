import stainless.lang._
import stainless.proof._
import stainless.annotation._

object SuperCall5 {

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
    x + Zero == x
  }.holds

  def lemma_associativity_plus(@induct x: Nat, y: Nat, z: Nat): Boolean = {
    x + (y + z) == (x + y) + z
  }.holds

  // The laws are ghost: their overrides call the missing implementations through `super`,
  // which executable code may not do.
  abstract class Monoid {
    def empty: Nat
    def append(x: Nat, y: Nat): Nat

    @ghost
    def law_leftIdentity(x: Nat) = (??? : Boolean).ensuring { res =>
      res && append(empty, x) == x
    }

    @ghost
    def law_rightIdentity(x: Nat) = (??? : Boolean).ensuring { res =>
      res && append(x, empty) == x
    }

    @ghost
    def law_associativity(x: Nat, y: Nat, z: Nat) = (??? : Boolean).ensuring { res =>
      res && append(x, append(y, z)) == append(append(x, y), z)
    }
  }

  case class AdditiveMonoid() extends Monoid {
    def empty = Zero

    def append(x: Nat, y: Nat) = x + y

    @ghost
    override def law_leftIdentity(x: Nat) = super.law_leftIdentity(x).holds

    @ghost
    override def law_rightIdentity(x: Nat) = {
      super.law_rightIdentity(x).because(lemma_rightIdentity_plus(x))
    }.holds

    @ghost
    override def law_associativity(x: Nat, y: Nat, z: Nat) = {
      super.law_associativity(x, y, z).because(lemma_associativity_plus(x, y, z))
    }.holds
  }

}
