import stainless.lang._
import stainless.equations._
import stainless.annotation._

object GodelNumbering {
  sealed abstract class Nat {
    def +(that: Nat): Nat = {
      decreases(this)
      this match {
        case Zero => that
        case Succ(n) => Succ(n + that)
      }
    }

    def *(that: Nat): Nat = {
      decreases(this)
      this match {
        case Zero => Zero
        case Succ(n) => (n * that) + that
      }
    }

    def -(that: Nat): Nat = {
      decreases(this)
      ((this, that) match {
        case (Succ(n1), Succ(n2)) => n1 - n2
        case _ => this
      })
    } ensuring { res =>
      res.repr <= repr &&
      ((this > Zero && that > Zero) ==> res.repr < repr)
    }

    def <(that: Nat): Boolean = {
      decreases(this)
        ((this, that) match {
        case (Succ(n1), Succ(n2)) => n1 < n2
        case (Zero, Succ(_)) => true
        case _ => false
      })
    } ensuring (_ == repr < that.repr)

    def <=(that: Nat): Boolean = (this < that) || (this == that)
    def >(that: Nat): Boolean = !(this < that) && (this != that)
    def >=(that: Nat): Boolean = (this > that) || (this == that)

    def /(that: Nat): Nat = {
      require(that > Zero)
      decreases(repr)
      if (this < that) Zero else
      Succ((this - that) / that)
    } ensuring { res =>
      res.repr <= repr &&
      ((this > Zero && that > One) ==> res.repr < repr)
    }

    def %(that: Nat): Nat = {
      require(that > Zero)
      decreases(repr)
      if (this < that) this
      else (this - that) % that
    }

    def repr: BigInt = {
      decreases(this)
      this match {
        case Zero => BigInt(0)
        case Succ(n) => n.repr + BigInt(1)
      }
     } ensuring (_ >= BigInt(0))
  }

  case object Zero extends Nat
  case class Succ(n: Nat) extends Nat

  val One = Succ(Zero)
  val Two = Succ(One)

  @induct
  def plus_zero(n: Nat): Boolean = {
    n + Zero == n
  }.holds
  def zero_plus(n: Nat): Boolean = { Zero + n == n }.holds

  @induct
  def minus_identity(n: Nat): Boolean = {
    n - n == Zero
  }.holds

  @induct
  def associative_plus(n1: Nat, n2: Nat, n3: Nat): Boolean = {
    (n1 + n2) + n3 == n1 + (n2 + n3)
  }.holds

  def commutative_plus(n1: Nat, n2: Nat): Boolean = {
    decreases(n1, n2)
    n1 match {
      case Zero => zero_plus(n2) && plus_zero(n2)
      case Succ(p1) => n2 match {
        case Zero => zero_plus(p1) && plus_zero(p1)
        case Succ(p2) => commutative_plus(n1, p2) && commutative_plus(p1, n2)
      }
    }
    n1 + n2 == n2 + n1
  }.holds

  def distributive_times(n1: Nat, n2: Nat, n3: Nat): Boolean = {
    decreases(n1)
    n1 * (n2 + n3) == (n1 * n2) + (n1 * n3) because (n1 match {
      case Zero => true
      case Succ(p1) => {
        Succ(p1) * (n2 + n3)       ==:| trivial |:
        p1 * (n2 + n3) + (n2 + n3) ==:| distributive_times(p1, n2, n3) |:
        (p1 * n2) + (p1 * n3) + (n2 + n3) ==:| associative_plus((p1 * n2) + (p1 * n3), n2, n3) |:
        (p1 * n2) + (p1 * n3) + n2 + n3 ==:| associative_plus(p1 * n2, p1 * n3, n2) |:
        (p1 * n2) + ((p1 * n3) + n2) + n3 ==:| commutative_plus(p1 * n3, n2) |:
        (p1 * n2) + (n2 + (p1 * n3)) + n3 ==:| associative_plus(p1 * n2, n2, p1 * n3) |:
        ((p1 * n2) + n2) + (p1 * n3) + n3 ==:| associative_plus((p1 * n2) + n2, p1 * n3, n3) |:
        ((p1 * n2) + n2) + ((p1 * n3) + n3) ==:| trivial |:
        (n1 * n2) + (n1 * n3)
      }.qed
    })
  }.holds

  def commutative_times(n1: Nat, n2: Nat): Boolean = {
    decreases(n1,n2)
    (n1 * n2 == n2 * n1) because ((n1, n2) match {
      case (Zero, Zero) => true
      case (Zero, Succ(p2)) => commutative_times(n1, p2)
      case (Succ(p1), Zero) => commutative_times(p1, n2)
      case (Succ(p1), Succ(p2)) => {
        n1 * n2               ==:| trivial                                                      |:
        (p1 * n2) + n2        ==:| commutative_times(p1, n2)                                    |:
        (n2 * p1) + n2        ==:| trivial                                                      |:
        ((p2 * p1) + p1) + n2 ==:| commutative_times(p1, p2)                                    |:
        ((p1 * p2) + p1) + n2 ==:| associative_plus(p1 * p2, p1, n2)                            |:
        (p1 * p2) + (p1 + n2) ==:| commutative_plus(p1, n2)                                     |:
        (p1 * p2) + (n2 + p1) ==:| (associative_plus(p2, One, p1) && commutative_plus(p2, One)) |:
        (p1 * p2) + (p2 + n1) ==:| associative_plus(p1 * p2, p2, n1)                            |:
        ((p1 * p2) + p2) + n1 ==:| trivial                                                      |:
        (n1 * p2) + n1        ==:| commutative_times(n1, p2)                                    |:
        (p2 * n1) + n1        ==:| trivial                                                      |:
        n2 * n1
      }.qed
    })
  }.holds

  def distributive_times2(n1: Nat, n2: Nat, n3: Nat): Boolean = {
    commutative_times(n1 + n2, n3)
    distributive_times(n3, n1, n2)
    commutative_times(n1, n3)
    commutative_times(n2, n3)

    (n1 + n2) * n3 == (n1 * n3) + (n2 * n3)
  }.holds

  def associative_times(n1: Nat, n2: Nat, n3: Nat): Boolean = {
    decreases(n1)
    (n1 * (n2 * n3) == (n1 * n2) * n3) because (n1 match {
      case Zero => true
      case Succ(p1) => {
        n1 * (n2 * n3)               ==:|                       trivial |:
        (p1 * (n2 * n3)) + (n2 * n3) ==:| associative_times(p1, n2, n3) |:
        ((p1 * n2) * n3) + (n2 * n3) ==:| commutative_plus((p1 * n2) * n3, n2 * n3) |:
        (n2 * n3) + ((p1 * n2) * n3) ==:| distributive_times2(n2, p1 * n2, n3) |:
        (n2 + (p1 * n2)) * n3        ==:| commutative_plus(n2, p1 * n2) |:
        ((p1 * n2) + n2) * n3        ==:| trivial |:
        (n1 * n2) * n3
      }.qed
    })
  }.holds

  def succ_<(n1: Nat, n2: Nat): Boolean = {
    require(n1 <= n2)
    decreases(n1)
    (n1 < Succ(n2)) because (n1 match {
      case Zero => true
      case Succ(n) =>
        val Succ(p2) = n2
        succ_<(n, p2)
    })
  }.holds

  def succ_<=(n1: Nat, n2: Nat): Boolean = {
    require(n1 < n2)
    decreases(n2)
    Succ(n1) <= n2 because (n2 match {
      case Succ(p2) if n1 != p2 => pred_<(n1, n2) && succ_<=(n1, p2)
      case _ => true
    })
  }.holds

  def pred_<(n1: Nat, n2: Nat): Boolean = {
    require(n1 < n2)
    decreases(n1)
    val Succ(n) = n2
    ((n1 != n) ==> (n1 < n)) because (n2 match {
      case Succ(n) if n == n1 => true
      case Succ(p2) => n1 match {
        case Zero => true
        case Succ(p1) => pred_<(p1, p2)
      }
    })
  }.holds

  def pred_<=(n1: Nat, n2: Nat): Boolean = {
    require(n1 > Zero && n1 <= n2)
    decreases(n1)
    val Succ(p1) = n1
    p1 < n2 because succ_<(p1, p1) && (n1 == n2 || transitive_<(p1, n1, n2))
  }.holds

  def transitive_<(n1: Nat, n2: Nat, n3: Nat): Boolean = {
    require(n1 < n2 && n2 < n3)
    decreases(n3)
    (n1 < n3) because (n3 match {
      case Zero => true
      case Succ(n) if n == n2 => succ_<(n1, n)
      case Succ(n) => pred_<(n2, n3) && transitive_<(n1, n2, n) && succ_<(n1, n)
    })
  }.holds

  def antisymmetric_<(n1: Nat, n2: Nat): Boolean = {
    decreases(n1)
    n1 < n2 == !(n2 <= n1) because ((n1, n2) match {
      case (Succ(p1), Succ(p2)) => antisymmetric_<(p1, p2)
      case _ => true
    })
  }.holds

  def plus_succ(n1: Nat, n2: Nat): Boolean = {
    n1 + Succ(n2)   ==:| associative_plus(n1, One, n2) |:
    (n1 + One) + n2 ==:| commutative_plus(n1, One)     |:
    (One + n1) + n2 ==:| associative_plus(One, n1, n2) |:
    (Succ(n1 + n2): Nat)
  }.qed

  def plus_<(n1: Nat, n2: Nat, n3: Nat): Boolean = {
    require(n2 < n3)
    decreases(n3)
    (n1 + n2 < n1 + n3) because (n3 match {
      case Succ(p3) if n2 == p3 => plus_succ(n1, n2) && succ_<(n1 + n2, n1 + n2)
      case Succ(p3) => plus_succ(n1, p3) && pred_<(n2, n3) && plus_<(n1, n2, p3) && succ_<(n1 + n2, n1 + p3)
    })
  }.holds

  def plus_<(n1: Nat, n2: Nat, n3: Nat, n4: Nat): Boolean = {
    require(n1 <= n3 && n2 <= n4)
    decreases(n3)
    n1 + n2 <= n3 + n4 because (n3 match {
      case Zero => trivial
      case Succ(_) if n1 == n3 && n2 == n4 => trivial
      case Succ(_) if n1 == n3 => plus_<(n1, n2, n4)
      case Succ(p3) => pred_<(n1, n3) && plus_<(n1, n2, p3, n4) && succ_<(n1 + n2, p3 + n4)
    })
  }.holds

  def associative_plus_minus(n1: Nat, n2: Nat, n3: Nat): Boolean = {
    require(n2 >= n3)
    decreases(n2)
    (n1 + n2) - n3 == n1 + (n2 - n3) because ((n2, n3) match {
      case (Succ(p2), Succ(p3)) =>
        {
          (n1 + Succ(p2)) - Succ(p3)    ==:|          commutative_plus(One, p2) |:
          (n1 + (p2 + One)) - Succ(p3)  ==:|      associative_plus(n1, p2, One) |:
          ((n1 + p2) + One) - Succ(p3)  ==:|     commutative_plus(n1 + p2, One) |:
          Succ(n1 + p2) - Succ(p3)      ==:|                            trivial |:
          (n1 + p2) - p3                ==:| associative_plus_minus(n1, p2, p3) |:
          n1 + (p2 - p3)                ==:|                            trivial |:
          n1 + (n2 - n3)
        }.qed
      case _ => true
    })
  }.holds

  def additive_inverse(n1: Nat, n2: Nat): Boolean = {
    n1 + n2 - n2 == n1
  }.holds because (associative_plus_minus(n1, n2, n2) && minus_identity(n2) && plus_zero(n1))

  def multiplicative_inverse(n1: Nat, n2: Nat): Boolean = {
    require(n2 > Zero)
    decreases(n1)
    (n1 * n2) / n2 == n1 because (n1 match {
      case Succ(p1) =>
        {
          (n1 * n2) / n2                           ==:| trivial                                                   |:
          (p1 * n2 + n2) / n2                      ==:|
            (commutative_plus(p1 * n2, n2) && increasing_plus(n2, p1 * n2) && antisymmetric_<(p1 * n2 + n2, n2)) |:
          (Succ(((p1 * n2 + n2) - n2) / n2) : Nat) ==:| additive_inverse(p1 * n2, n2)                             |:
          (Succ((p1 * n2) / n2)             : Nat) ==:| multiplicative_inverse(p1, n2)                            |:
          n1
        }.qed

      case _ => true
    })
  }.holds

  @induct
  def increasing_plus(n1: Nat, n2: Nat): Boolean = {
    n1 <= n1 + n2
  }.holds

  @induct
  def increasing_plus_strict(n1: Nat, n2: Nat): Boolean = {
    require(n2 > Zero)
    n1 < n1 + n2
  }.holds

  def increasing_times(n1: Nat, n2: Nat): Boolean = {
    require(n1 > Zero && n2 > Zero)
    decreases(n1)
    n1 <= n1 * n2 because (n1 match {
      case Succ(Zero) => true
      case Succ(p1) =>
        assert(increasing_times(p1, n2))
        assert(increasing_plus_strict(p1 * n2, n2))
        assert(p1 == p1 * n2 || transitive_<(p1, p1 * n2, p1 * n2 + n2))
        assert(succ_<=(p1, p1 * n2 + n2))
        (n1 <= n1 * n2 ==:| trivial |: true).qed
    })
  }.holds

  def pow(n1: Nat, n2: Nat): Nat = {
    decreases(n2)
    n2 match {
      case Succ(n) => n1 * pow(n1, n)
      case Zero => One
    }
  }

  def pow_positive(n1: Nat, n2: Nat): Boolean = {
    require(n1 > Zero)
    decreases(n2)
    pow(n1, n2) > Zero because (n2 match {
      case Succ(p2) => pow_positive(n1, p2) && increasing_times(n1, pow(n1, p2))
      case _ => true
    })
  }.holds

  def isEven(n: Nat): Boolean = {
    decreases(n)
    n match {
      case Zero => true
      case Succ(Zero) => false
      case Succ(n) => !isEven(n)
    }
  }

  def times_two_even(n: Nat): Boolean = {
    decreases(n)
    isEven(Two * n) because (n match {
      case Zero => true
      case Succ(p) => {
        isEven(Two * n)       ==:| commutative_times(Two, n)      |:
        isEven(n * Two)       ==:| trivial                        |:
        isEven(p * Two + Two) ==:| commutative_plus(p * Two, Two) |:
        isEven(p * Two)       ==:| commutative_times(Two, p)      |:
        isEven(Two * p)       ==:| times_two_even(p)              |:
        true
      }.qed
    })
  }.holds

  def times_two_plus_one_odd(n: Nat): Boolean = {
    !isEven(Two * n + One) because times_two_even(n) && commutative_plus(Two * n, One)
  }.holds

  def power_two_even(n: Nat): Boolean = {
    require(n > Zero)
    isEven(pow(Two, n)) because (n match {
      case Succ(p) => times_two_even(pow(Two, p))
    })
  }.holds

  def pair(n1: Nat, n2: Nat): Nat = pow(Two, n1) * (Two * n2 + One) - One

  def log2_and_remainder(n: Nat): (Nat, Nat) = {
    decreases(n.repr)
    if (isEven(n) && n > Zero) {
      val (a, b) = log2_and_remainder(n / Two)
      (Succ(a), b)
    } else {
      (Zero, n)
    }
  }

  def project(n: Nat): (Nat, Nat) = {
    val (a, b) = log2_and_remainder(Succ(n))
    (a, (b - One) / Two)
  }

  def project_1_inverse(n1: Nat, n2: Nat): Boolean = {
    decreases(n1)
    log2_and_remainder(Succ(pair(n1, n2))) == (n1, (Two * n2 + One)) because (n1 match {
      case Succ(p1) =>
        def assoc_plus_minus_one(n: Nat): Boolean = {
          One + (pow(Two, n) * (Two * n2 + One) - One) == (One + pow(Two, n) * (Two * n2 + One)) - One because {
            pow_positive(Two, n) &&
            commutative_plus(Two * n2, One) &&
            increasing_times(pow(Two, n), (Two * n2 + One)) &&
            associative_plus_minus(One, pow(Two, n) * (Two * n2 + One), One)
          }
        }.holds

        {
          log2_and_remainder(Succ(pair(n1, n2)))                                  ==:|
                                                                            trivial |:
          log2_and_remainder(Succ(pow(Two, n1) * (Two * n2 + One) - One))         ==:|
                                                                            trivial |:
          log2_and_remainder(One + (pow(Two, n1) * (Two * n2 + One) - One))       ==:|
                                                           assoc_plus_minus_one(n1) |:
          log2_and_remainder((One + pow(Two, n1) * (Two * n2 + One)) - One)       ==:|
                             commutative_plus(One, pow(Two, n1) * (Two * n2 + One)) |:
          log2_and_remainder(pow(Two, n1) * (Two * n2 + One) + One - One)         ==:|
                             additive_inverse(pow(Two, n1) * (Two * n2 + One), One) |:
          log2_and_remainder(pow(Two, n1) * (Two * n2 + One))                     ==:|
                                                                            trivial |:
          log2_and_remainder((Two * pow(Two, p1)) * (Two * n2 + One))             ==:|
                               associative_times(Two, pow(Two, p1), Two * n2 + One) |:
          log2_and_remainder(Two * (pow(Two, p1) * (Two * n2 + One)))             ==:|
                             additive_inverse(pow(Two, p1) * (Two * n2 + One), One) |:
          log2_and_remainder(Two * (pow(Two, p1) * (Two * n2 + One) + One - One)) ==:|
                             commutative_plus(One, pow(Two, p1) * (Two * n2 + One)) |:
          log2_and_remainder(Two * (One + pow(Two, p1) * (Two * n2 + One) - One)) ==:|
                                                           assoc_plus_minus_one(p1) |:
          log2_and_remainder(Two * Succ(pow(Two, p1) * (Two * n2 + One) - One))   ==:|
                                                                            trivial |:
          log2_and_remainder(Two * Succ(pair(p1, n2)))                            ==:|
                                             (times_two_even(Succ(pair(p1, n2))) &&
                                                       project_1_inverse(p1, n2) &&
                                      commutative_times(Two, Succ(pair(p1, n2))) &&
                                   multiplicative_inverse(Succ(pair(p1, n2)), Two)) |:
          (n1, Two * n2 + One)
        }.qed

      case _ =>
        {
          log2_and_remainder(Succ(pair(n1, n2)))                                  ==:|
                                                                            trivial |:
          log2_and_remainder(Succ(pow(Two, n1) * (Two * n2 + One) - One))         ==:|
                                                                            trivial |:
          log2_and_remainder(Succ(Two * n2 + One - One))                          ==:|
                                                    additive_inverse(Two * n2, One) |:
          log2_and_remainder(Succ(Two * n2))                                      ==:|
                                                         times_two_plus_one_odd(n2) |:
          ((Zero, Succ(Two * n2)): (Nat, Nat))                                    ==:|
                                                    commutative_plus(Two * n2, One) |:
          ((Zero, Two * n2 + One): (Nat, Nat))
        }.qed
    })
  }.holds

  def inverse_lemma(n1: Nat, n2: Nat): Boolean = {
    project(pair(n1, n2)) == (n1, n2)
  }.holds because {
    val (p1, remainder) = log2_and_remainder(Succ(pair(n1, n2)))
    val p2 = (remainder - One) / Two

    project(pair(n1, n2))                ==:| trivial                         |:
    (p1, p2)                             ==:| trivial                         |:
    (p1, (remainder - One) / Two)        ==:| project_1_inverse(n1, n2)       |:
    (n1, ((Two * n2 + One) - One) / Two) ==:| additive_inverse(Two * n2, One) |:
    (n1, (Two * n2) / Two)               ==:| commutative_times(Two, n2)      |:
    (n1, (n2 * Two) / Two)               ==:| multiplicative_inverse(n2, Two) |:
    (n1, n2)
  }.qed

  def pair_unique(n1: Nat, n2: Nat, n3: Nat, n4: Nat): Boolean = {
    (pair(n1, n2) == pair(n3, n4)) == ((n1, n2) == (n3, n4))
  }.holds because {
    if (pair(n1, n2) == pair(n3, n4)) {
      assert(project(pair(n1, n2)) == project(pair(n3, n4)))
      assert(inverse_lemma(n1, n2) && inverse_lemma(n3, n4))
      assert((n1, n2) == (n3, n4))
      ((n1, n2) == (n3, n4) ==:| trivial |: true).qed
    } else {
      assert((n1, n2) != (n3, n4))
      ((n1, n2) == (n3, n4) ==:| trivial |: false).qed
    }
  }
}
