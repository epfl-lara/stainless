package sf1

import stainless.lang._ // for the holds keyword
import stainless.proof._ // for the check keyword
import scala.language.postfixOps // to avoid warnings about postfix holds

import stainless.annotation._ // for the @induct annotation

import Basics._

object Induction {

  // This theorem requires a proof by induction. To use the induction
  // hypothesis, we make a recursive call to the function, with the argument
  // for which we want to use the inductive hypothesis (here, n2)
  def plus_n_O(n: Nat): Boolean = {
    decreases(n)
    n match {
      case O => ()
      case S(n2) => check(plus_n_O(n2))
    }

    n + O == n
  }.holds

  // For such simple examples, Stainless also supports an @induct annotation,
  // that tells Stainless to use the inductive hypothesis.

  @induct
  def plus_n_O_auto(n: Nat): Boolean = {
    n + O == n
  }.holds

  // minus_diag is defined in Basics.scala

  /** **** Exercise: 2 stars, recommended (basic_induction)  */

  @induct
  def mult_0_r(n: Nat) = {
    n * O == O
  }.holds

  @induct
  def plus_n_Sm(n: Nat, m: Nat) = {
    S (n + m) == n + (S(m))
  }.holds

  // here, we do the induction manually, as we need to use the previous lemma
  // during the induction
  def plus_comm(n: Nat, m: Nat): Boolean = {
    decreases(n)
    n match {
      case O => check(plus_n_O(m))
      case S(n2) =>
        check(plus_comm(n2,m)) // induction hypothesis: n2 + m == m + n2
        check(plus_n_Sm(m,n2)) // S(m + n2) == m + S(n2)
    }
    n + m == m + n
  }.holds

  @induct
  def plus_assoc(n: Nat, m: Nat, p: Nat) = {
    n + (m + p) == (n + m) + p
  }.holds

  /** [] */

  /** **** Exercise: 2 stars (double_plus)  */

  def double(n: Nat): Nat = {
    decreases(n)
    n match {
      case O => O
      case S(n2) => S(S(double(n2)))
    }
  }

  def double_plus(n: Nat): Boolean = {
    decreases(n)
    n match {
      case O => ()
      case S(n2) =>
        check(double_plus(n2))
        check(plus_n_Sm(n,n))
    }

    double(n) == n + n
  }.holds

  /** [] */


  /** **** Exercise: 2 stars, optional (evenb_S)  */

  @induct
  def evenb_S(n: Nat): Boolean = {
    evenb (S(n)) == !evenb(n)
  }.holds

  /** [] */


  def mult_0_plus2(n: Nat, m: Nat): Boolean = {
    assert (O + n == n) // this is not really required here
    (O + n) * m == n * m
  }.holds

  def plus_rearrange(n: Nat, m: Nat, p: Nat, q: Nat): Boolean = {
    check(plus_comm(n,m)) // asserts that n+m == m+n
    (n + m) + (p + q) == (m + n) + (p + q)
  }.holds

  /** **** Exercise: 3 stars, recommended (mult_comm)  */

  def plus_swap(n: Nat, m: Nat, p: Nat): Boolean = {
    plus_comm(n,m+p) // n + (m+p) == (m+p) + n
    plus_assoc(m,p,n) // (m+p) + n == m+(p+n)
    plus_comm(p,n) // p+n = n+p

    n + (m + p) == m + (n + p)
  }.holds

  def mult_n_Sm(n: Nat, m: Nat): Boolean = {
    decreases(n)
    n match {
      case O => ()
      case S(n2) =>
        // By definition n * S(m) = S(n2) * S(m) = S(m) + n2 * S(m) = S(m + n2 * S(m))
        mult_n_Sm(n2, m) // by induction hypothesis: we know n2*S(m) = n2 + n2*m
        // therefore, n * S(m) = S(m + (n2 + n2*m))
        plus_swap(m,n2,n2*m) // m + (n2 + n2*m) = n2 + (m + n2 * m)
    }
    n * S(m) == n + n * m
  }.holds

  def mult_comm(n: Nat, m: Nat): Boolean = {
    decreases(n)
    n match {
      case O =>
        check(mult_0_r(m))
      case S(n2) =>
        check(mult_comm(n2,m))
        check(mult_n_Sm(m,n2))
        // these assertions are not needed, but show the steps of the proof
        // assert(n * m == m + n2 * m) // by defininition
        // assert(n * m == m + m * n2) // by mult_comm
        // assert(m * S(n2) == m + m * n2) // by mult_n_Sm
        // assert(m * n == m + m * n2) // because S(n2) == n
        // assert(n * m == m * n)
    }

    n * m == m * n
  }.holds

  /** [] */


  /** **** Exercise: 3 stars, optional (more_exercises)  */

  // For these exercises, we use the Bool type defined in Basics, rather than
  // the native Boolean type

  @induct
  def leb_refl(n: Nat) = {
    leb(n,n)
  }.holds

  def zero_nbeq_S(n: Nat) = {
    !beq_nat(O,S(n))
  }.holds

  def andb_false_r(b: Bool) = {
    andb(b,False) == False
  }.holds

  @induct
  def plus_ble_compat_l(p: Nat, n: Nat, m: Nat) = {
    require(leb(n,m))

    leb(p+n,p+m)
  }.holds

  def S_nbeq_0(n: Nat) = {
    !beq_nat(S(n), O)
  }.holds

  def mult_1_l(n: Nat) = {
    plus_n_O(n)
    one * n == n
  }.holds

  def all3_spec(b: Bool, c: Bool) = {
    orb(
      andb(b,c),
      orb(negb(b),negb(c))
    ) == True
  }.holds

  def mult_plus_distr_r(n: Nat, m: Nat, p: Nat): Boolean = {
    decreases(n)
    n match {
      case O => ()
      case S(n2) =>
        // induction hypothesis: (n2 + m) * p = (n2 * p) + (m * p)
        check(mult_plus_distr_r(n2, m, p))
        check(plus_assoc(p, n2 * p, m * p)) // associativity

        // these assertions show the reasoning, but are not required for the
        // proof to go through
        // assert((n + m) * p == (S(n2 + m) * p)) // by definition of +
        // assert((n + m) * p == p + (n2 + m) * p) // by definition of *
        // assert((n + m) * p == p + (n2 * p + m * p)) // by induction hypothesis
        // assert((n + m) * p == p + n2 * p + m * p) // by associativity
        // assert((n + m) * p == (n * p) + (m * p)) // by definition of *
    }
    (n + m) * p == (n * p) + (m * p)
  }.holds

  def mult_assoc(n: Nat, m: Nat, p: Nat): Boolean = {
    decreases(n)
    n match {
      case O => ()
      case S(n2) =>
        check(mult_assoc(n2, m, p)) // induction hypothesis
        check(mult_plus_distr_r(m, n2 * m, p))

        // these assertions show the reasoning, but are not required
        // assert(n * (m * p) == m * p + n2 * (m * p)) // by definition of *
        // assert(n * (m * p) == m * p + (n2 * m) * p) // by induction hypothesis
        // assert(n * (m * p) == (m + n2 * m) * p) // by mult_plus_distr_r
        // assert(n * (m * p) == (n * m) * p) // by definition of *

    }

    n * (m * p) == (n * m) * p
  }.holds

  /** [] */

  /** **** Exercise: 2 stars, optional (beq_nat_refl)  */

  @induct
  def beq_nat_refl(n: Nat) = {
    beq_nat(n,n)
  }.holds

  /** [] */

  /** **** Exercise: 3 stars, recommended (binary_commute)  */

  def bin_incr(b: Bin): Boolean = {
    decreases(b)
    b match {
      case TwicePlusOne(b2) =>
        check(bin_incr(b2)) // induction hypothesis
        check(plus_n_Sm(bin_to_nat(b2), bin_to_nat(b2)))

        // these assertions show the reasoning, but are not required
        // assert(bin_to_nat(incr(b)) == bin_to_nat(Twice(incr(b2)))) // by definition of incr
        // assert(bin_to_nat(incr(b)) == bin_to_nat(incr(b2)) + bin_to_nat(incr(b2))) // by definition of bin_to_nat
        // assert(bin_to_nat(incr(b)) == S(bin_to_nat(b2)) + S(bin_to_nat(b2))) // by induction hypothesis
        // assert(bin_to_nat(incr(b)) == S(bin_to_nat(b2) + S(bin_to_nat(b2)))) // by definition of +
        // assert(bin_to_nat(incr(b)) == S(S(bin_to_nat(b2) + bin_to_nat(b2)))) // by plus_n_Sm
        // assert(bin_to_nat(incr(b)) == S(bin_to_nat(b))) // by definition of bin_to_nat

      case _ => ()
    }

    bin_to_nat(incr(b)) == S(bin_to_nat(b))
  }.holds

  /** [] */

  /** **** Exercise: 5 stars, advanced (binary_inverse)  */

  /** (a) */

  def nat_to_bin(n: Nat): Bin = {
    decreases(n)
    n match {
      case O => Z
      case S(n2) => incr(nat_to_bin(n2))
    }
  }

  def nat_to_bin_to_nat(n: Nat): Boolean = {
    decreases(n)
    n match {
      case O => ()
      case S(n2) =>
        check(nat_to_bin_to_nat(n2)) // induction hypothesis
        check(bin_incr(nat_to_bin(n2))) // lemma

        // these assertions show the reasoning, but are not required
        // assert(bin_to_nat(nat_to_bin(n)) == bin_to_nat(incr(nat_to_bin(n2)))) // by definition of nat_to_bin
        // assert(bin_to_nat(nat_to_bin(n)) == S(bin_to_nat(nat_to_bin(n2)))) // by definition of nat_to_bin
        // assert(bin_to_nat(nat_to_bin(n)) == S(n2)) // by induction hypothesis
        // assert(bin_to_nat(nat_to_bin(n)) == n)
    }

    bin_to_nat(nat_to_bin(n)) == n
  }.holds

  /** (c) */

  def z_or_twice(b: Bin) = b match {
    case Z => Z
    case _ => Twice(b)
  }

  def normalize(b: Bin): Bin = {
    decreases(b)
    b match {
      case Z => Z
      case Twice(b2) => z_or_twice(normalize(b2))
      case TwicePlusOne(b2) => TwicePlusOne(normalize(b2))
    }
  }

  def plus_bin(a: Bin, b: Bin): Bin = {
    decreases(a)
    (a,b) match {
      case (Z,_) => b
      case (_,Z) => a
      case (Twice(a2), Twice(b2)) => Twice(plus_bin(a2,b2))
      case (Twice(a2), TwicePlusOne(b2)) => TwicePlusOne(plus_bin(a2,b2))
      case (TwicePlusOne(a2), Twice(b2)) => TwicePlusOne(plus_bin(a2,b2))
      case (TwicePlusOne(a2), TwicePlusOne(b2)) => Twice(incr(plus_bin(a2,b2)))
    }
  }

  def plus_bin_incr_l(a: Bin, b: Bin): Boolean = {
    decreases(a)
    a match {
      case Z => ()
      case Twice(a2) => ()
      case TwicePlusOne(a2) =>
        b match {
          case Z => ()
          case Twice(b2) =>
            check(plus_bin_incr_l(a2,b2)) // induction hypothesis needed in this case
          case TwicePlusOne(b2) =>
            check(plus_bin_incr_l(a2,b2)) // induction hypothesis needed in this case
        }
    }

    incr(plus_bin(a,b)) == plus_bin(incr(a),b)
  }.holds


  def nat_to_bin_plus(a: Nat, b: Nat): Boolean = {
    decreases(a)
    a match {
      case O => ()
      case S(a2) =>
        check(nat_to_bin_plus(a2,b)) // induction hypothesis
        check(plus_bin_incr_l(nat_to_bin(a2), nat_to_bin(b))) // call to lemma

        // these assertions show the reasoning, but are not required
        // assert(nat_to_bin(a+b) == nat_to_bin(S(a2+b))) // by definition of +
        // assert(nat_to_bin(a+b) == incr(nat_to_bin((a2+b)))) // by definition of nat_to_bin
        // assert(nat_to_bin(a+b) == incr(plus_bin(nat_to_bin(a2), nat_to_bin(b)))) // by induction hypothesis
        // assert(nat_to_bin(a+b) == plus_bin(incr(nat_to_bin(a2)), nat_to_bin(b))) // by lemma plus_bin_incr_l
        // assert(nat_to_bin(a+b) == plus_bin(nat_to_bin(S(a2)), nat_to_bin(b))) // by definition of nat_to_bin
        // assert(nat_to_bin(a+b) == plus_bin(nat_to_bin(a), nat_to_bin(b))) // qed
    }

    nat_to_bin(a+b) == plus_bin(nat_to_bin(a), nat_to_bin(b))
  }.holds

  def bin_to_nat_to_bin(b: Bin): Boolean = {
    decreases(b)

    b match {
      case Z => ()
      case Twice(b2) =>
        check(nat_to_bin_plus(bin_to_nat(b2), bin_to_nat(b2))) // call to lemma
        check(bin_to_nat_to_bin(b2)) // induction hypothesis

        // these assertions show the reasoning, but are not required
        // assert(nat_to_bin(bin_to_nat(b)) == nat_to_bin(bin_to_nat(b2) + bin_to_nat(b2))) // by definition of bin_to_nat
        // assert(nat_to_bin(bin_to_nat(b)) == plus_bin(nat_to_bin(bin_to_nat(b2)),nat_to_bin(bin_to_nat(b2)))) // by lemma nat_to_bin_plus
        // assert(nat_to_bin(bin_to_nat(b)) == plus_bin(normalize(b2),normalize(b2))) // by induction hypothesis
        // assert(nat_to_bin(bin_to_nat(b)) == z_or_twice(normalize(b2))) // by case analysis on b2, and using assertions from inside the inductive call
        // assert(nat_to_bin(bin_to_nat(b)) == normalize(b)) // by definition of normalize
      case TwicePlusOne(b2) =>
        check(nat_to_bin_plus(bin_to_nat(b2), bin_to_nat(b2))) // call to lemma
        check(bin_to_nat_to_bin(b2)) // induction hypothesis

        // these assertions show the reasoning, but are not required
        // assert(nat_to_bin(bin_to_nat(b)) == nat_to_bin(S(bin_to_nat(b2) + bin_to_nat(b2)))) // by definition of bin_to_nat
        // assert(nat_to_bin(bin_to_nat(b)) == incr(nat_to_bin(bin_to_nat(b2) + bin_to_nat(b2)))) // by definition of nat_to_bin
        // assert(nat_to_bin(bin_to_nat(b)) == incr(plus_bin(nat_to_bin(bin_to_nat(b2)),nat_to_bin(bin_to_nat(b2))))) // by lemma nat_to_bin_plus
        // assert(nat_to_bin(bin_to_nat(b)) == incr(plus_bin(normalize(b2),normalize(b2)))) // by induction hypothesis
        // assert(nat_to_bin(bin_to_nat(b)) == incr(z_or_twice(normalize(b2)))) // by case analysis on b2, and using assertions from inside the inductive call
        // assert(nat_to_bin(bin_to_nat(b)) == TwicePlusOne(normalize(b2))) // by definitions of incr and z_or_twice
        // assert(nat_to_bin(bin_to_nat(b)) == normalize(b)) // by definition of normalize
    }

    nat_to_bin(bin_to_nat(b)) == normalize(b)
  }.holds

  /** [] */

  def main(args: Array[String]) {}

}
