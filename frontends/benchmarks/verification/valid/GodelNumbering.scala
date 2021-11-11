import stainless.lang._
import stainless.equations._
import stainless.annotation._
import stainless.proof.check

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

  @induct @opaque @inlineOnce
  def plus_zero(n: Nat): Unit = {
    ()
  }.ensuring(_ => n + Zero == n)

  @opaque @inlineOnce
  def zero_plus(n: Nat): Unit = {
    ()
  }.ensuring(_ => Zero + n == n)

  @opaque @inlineOnce
  def minus_identity(@induct n: Nat): Unit = {
    ()
  }.ensuring(_ =>
    n - n == Zero
  )

  @opaque @inlineOnce
  def associative_plus(@induct n1: Nat, n2: Nat, n3: Nat): Unit = {
    ()
  }.ensuring(_ => (n1 + n2) + n3 == n1 + (n2 + n3))

  @opaque @inlineOnce
  def plus_succ(@induct n1: Nat, n2: Nat): Unit = {
    ()
  }.ensuring(_ => n1 + Succ(n2) == Succ(n1 + n2))

  @opaque @inlineOnce
  def commutative_plus(n1: Nat, n2: Nat): Unit = {
    decreases(n1, n2)
    n1 match {
      case Zero =>
        plus_zero(n2)
      case Succ(p1) => {
        n1 + n2               ==:| trivial   |:
        Succ(p1) + n2         ==:| trivial   |:
        (Succ(p1 + n2): Nat)  ==:| commutative_plus(p1, n2) |:
        (Succ(n2 + p1): Nat)  ==:| plus_succ(n2, p1) |:
        n2 + Succ(p1)         ==:| trivial |:
        n2 + n1
      }.qed
    }
  }.ensuring(_ => n1 + n2 == n2 + n1)

  @opaque @inlineOnce
  def distributive_times(n1: Nat, n2: Nat, n3: Nat): Unit = {
    decreases(n1)
    n1 match {
      case Zero => ()
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
    }
  }.ensuring(_ => n1 * (n2 + n3) == (n1 * n2) + (n1 * n3))

  @opaque @inlineOnce
  def commutative_times(n1: Nat, n2: Nat): Unit = {
    decreases(n1,n2)
    (n1, n2) match {
      case (Zero, Zero) => ()
      case (Zero, Succ(p2)) => commutative_times(n1, p2)
      case (Succ(p1), Zero) => commutative_times(p1, n2)
      case (Succ(p1), Succ(p2)) => {
        n1 * n2               ==:| trivial                                                      |:
        (p1 * n2) + n2        ==:| commutative_times(p1, n2)                                    |:
        (n2 * p1) + n2        ==:| trivial                                                      |:
        ((p2 * p1) + p1) + n2 ==:| commutative_times(p1, p2)                                    |:
        ((p1 * p2) + p1) + n2 ==:| associative_plus(p1 * p2, p1, n2)                            |:
        (p1 * p2) + (p1 + n2) ==:| commutative_plus(p1, n2)                                     |:
        (p1 * p2) + (n2 + p1) ==:| { associative_plus(p2, One, p1); commutative_plus(p2, One) } |:
        (p1 * p2) + (p2 + n1) ==:| associative_plus(p1 * p2, p2, n1)                            |:
        ((p1 * p2) + p2) + n1 ==:| trivial                                                      |:
        (n1 * p2) + n1        ==:| commutative_times(n1, p2)                                    |:
        (p2 * n1) + n1        ==:| trivial                                                      |:
        n2 * n1
      }.qed
    }
  }.ensuring(_ => n1 * n2 == n2 * n1)

  @opaque @inlineOnce
  def distributive_times2(n1: Nat, n2: Nat, n3: Nat): Unit = {
    commutative_times(n1 + n2, n3)
    distributive_times(n3, n1, n2)
    commutative_times(n1, n3)
    commutative_times(n2, n3)

    ()
  }.ensuring(_ => (n1 + n2) * n3 == (n1 * n3) + (n2 * n3))

  @opaque @inlineOnce
  def associative_times(n1: Nat, n2: Nat, n3: Nat): Unit = {
    decreases(n1)
    n1 match {
      case Zero => ()
      case Succ(p1) => {
        n1 * (n2 * n3)               ==:|                       trivial |:
        (p1 * (n2 * n3)) + (n2 * n3) ==:| associative_times(p1, n2, n3) |:
        ((p1 * n2) * n3) + (n2 * n3) ==:| commutative_plus((p1 * n2) * n3, n2 * n3) |:
        (n2 * n3) + ((p1 * n2) * n3) ==:| distributive_times2(n2, p1 * n2, n3) |:
        (n2 + (p1 * n2)) * n3        ==:| commutative_plus(n2, p1 * n2) |:
        ((p1 * n2) + n2) * n3        ==:| trivial |:
        (n1 * n2) * n3
      }.qed
    }
  }.ensuring(_ => n1 * (n2 * n3) == (n1 * n2) * n3)

  @opaque @inlineOnce
  def succ_<(n1: Nat, n2: Nat): Unit = {
    require(n1 <= n2)
    decreases(n1)
    n1 match {
      case Zero => ()
      case Succ(n) =>
        val Succ(p2) = n2
        succ_<(n, p2)
    }
  }.ensuring(_ => n1 < Succ(n2))

  @opaque @inlineOnce
  def succ_<=(n1: Nat, n2: Nat): Unit = {
    require(n1 < n2)
    decreases(n2)
    n2 match {
      case Succ(p2) if n1 != p2 =>
        pred_<(n1, n2)
        succ_<=(n1, p2)
      case _ => ()
    }
  }.ensuring(_ => Succ(n1) <= n2)

  @opaque @inlineOnce
  def pred_<(n1: Nat, n2: Nat): Unit = {
    require(n1 < n2)
    decreases(n1)
    val Succ(n) = n2
    n2 match {
      case Succ(n) if n == n1 => ()
      case Succ(p2) => n1 match {
        case Zero => ()
        case Succ(p1) => pred_<(p1, p2)
      }
    }
  }.ensuring {_ =>
    val Succ(n) = n2
    (n1 != n) ==> (n1 < n)
  }

  @opaque @inlineOnce
  def pred_<=(n1: Nat, n2: Nat): Unit = {
    require(n1 > Zero && n1 <= n2)
    val Succ(p1) = n1
    succ_<(p1, p1)
    if (n1 != n2) transitive_<(p1, n1, n2)
  }.ensuring { _ =>
    val Succ(p1) = n1
    p1 < n2
  }

  @opaque @inlineOnce
  def transitive_<(n1: Nat, n2: Nat, n3: Nat): Unit = {
    require(n1 < n2 && n2 < n3)
    decreases(n3)
    n3 match {
      case Zero => ()
      case Succ(n) if n == n2 => succ_<(n1, n)
      case Succ(n) =>
        pred_<(n2, n3)
        transitive_<(n1, n2, n)
        succ_<(n1, n)
    }
  }.ensuring(_ => n1 < n3)

  @opaque @inlineOnce
  def antisymmetric_<(n1: Nat, n2: Nat): Unit = {
    decreases(n1)
    (n1, n2) match {
      case (Succ(p1), Succ(p2)) => antisymmetric_<(p1, p2)
      case _ => ()
    }
  }.ensuring(_ => n1 < n2 == !(n2 <= n1))

  @opaque @inlineOnce
  def plus_<(n1: Nat, n2: Nat, n3: Nat): Unit = {
    require(n2 < n3)
    decreases(n3)
    n3 match {
      case Succ(p3) if n2 == p3 =>
        plus_succ(n1, n2)
        succ_<(n1 + n2, n1 + n2)
      case Succ(p3) =>
        plus_succ(n1, p3)
        pred_<(n2, n3)
        plus_<(n1, n2, p3)
        succ_<(n1 + n2, n1 + p3)
    }
  }.ensuring(_ => n1 + n2 < n1 + n3)

  @opaque @inlineOnce
  def plus_<(n1: Nat, n2: Nat, n3: Nat, n4: Nat): Unit = {
    require(n1 <= n3 && n2 <= n4)
    decreases(n3)
    n3 match {
      case Zero => ()
      case Succ(_) if n1 == n3 && n2 == n4 => ()
      case Succ(_) if n1 == n3 => plus_<(n1, n2, n4)
      case Succ(p3) =>
        pred_<(n1, n3)
        plus_<(n1, n2, p3, n4)
        succ_<(n1 + n2, p3 + n4)
    }
  }.ensuring(_ => n1 + n2 <= n3 + n4)

  @opaque @inlineOnce
  def associative_plus_minus(n1: Nat, n2: Nat, n3: Nat): Unit = {
    require(n2 >= n3)
    decreases(n2)
    (n2, n3) match {
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
      case _ => ()
    }
  }.ensuring(_ => (n1 + n2) - n3 == n1 + (n2 - n3))

  @opaque @inlineOnce
  def additive_inverse(n1: Nat, n2: Nat): Unit = {
    associative_plus_minus(n1, n2, n2)
    minus_identity(n2)
    plus_zero(n1)
  }.ensuring(_ => n1 + n2 - n2 == n1)

  @opaque @inlineOnce
  def multiplicative_inverse(n1: Nat, n2: Nat): Unit = {
    require(n2 > Zero)
    decreases(n1)
    n1 match {
      case Succ(p1) =>
        {
          (n1 * n2) / n2                           ==:| trivial                                                   |:
          (p1 * n2 + n2) / n2                      ==:|
            { commutative_plus(p1 * n2, n2); increasing_plus(n2, p1 * n2); antisymmetric_<(p1 * n2 + n2, n2) }  |:
          (Succ(((p1 * n2 + n2) - n2) / n2) : Nat) ==:| additive_inverse(p1 * n2, n2)                             |:
          (Succ((p1 * n2) / n2)             : Nat) ==:| multiplicative_inverse(p1, n2)                            |:
          n1
        }.qed

      case _ => ()
    }
  }.ensuring(_ => (n1 * n2) / n2 == n1)

  @induct @opaque @inlineOnce
  def increasing_plus(n1: Nat, n2: Nat): Unit = {
    ()
  }.ensuring(_ => n1 <= n1 + n2)

  @induct @opaque @inlineOnce
  def increasing_plus_strict(n1: Nat, n2: Nat): Unit = {
    require(n2 > Zero)
    ()
  }.ensuring(_ => n1 < n1 + n2)

  @opaque @inlineOnce
  def increasing_times(n1: Nat, n2: Nat): Unit = {
    require(n1 > Zero && n2 > Zero)
    decreases(n1)
    n1 match {
      case Succ(Zero) => ()
      case Succ(p1) =>
        increasing_times(p1, n2)
        increasing_plus_strict(p1 * n2, n2)
        if (p1 != p1 * n2)
          transitive_<(p1, p1 * n2, p1 * n2 + n2)
        succ_<=(p1, p1 * n2 + n2)
        check(n1 <= n1 * n2)
        ()
    }
  }.ensuring(_ => n1 <= n1 * n2)

  def pow(n1: Nat, n2: Nat): Nat = {
    decreases(n2)
    n2 match {
      case Succ(n) => n1 * pow(n1, n)
      case Zero => One
    }
  }

  @opaque @inlineOnce
  def pow_positive(n1: Nat, n2: Nat): Unit = {
    require(n1 > Zero)
    decreases(n2)
    n2 match {
      case Succ(p2) =>
        pow_positive(n1, p2)
        increasing_times(n1, pow(n1, p2))
      case _ => ()
    }
  }.ensuring(_ => pow(n1, n2) > Zero)

  def isEven(n: Nat): Boolean = {
    decreases(n)
    n match {
      case Zero => true
      case Succ(Zero) => false
      case Succ(n) => !isEven(n)
    }
  }

  @opaque @inlineOnce
  def times_two_even(n: Nat): Unit = {
    decreases(n)
    n match {
      case Zero => ()
      case Succ(p) => {
        isEven(Two * n)       ==:| commutative_times(Two, n)      |:
        isEven(n * Two)       ==:| trivial                        |:
        isEven(p * Two + Two) ==:| commutative_plus(p * Two, Two) |:
        isEven(p * Two)       ==:| commutative_times(Two, p)      |:
        isEven(Two * p)       ==:| times_two_even(p)              |:
        true
      }.qed
    }
  }.ensuring(_ => isEven(Two * n))

  @opaque @inlineOnce
  def times_two_plus_one_odd(n: Nat): Unit = {
    times_two_even(n)
    assert(!isEven(One + Two * n))
    commutative_plus(Two * n, One)
  }.ensuring(_ => !isEven(Two * n + One))

  @opaque @inlineOnce
  def succ_times_two_odd(n: Nat): Unit = {
    times_two_plus_one_odd(n)
    commutative_plus(Two * n, One)
  }.ensuring(_ => !isEven(Succ(Two * n)))

  @opaque @inlineOnce
  def power_two_even(n: Nat): Unit = {
    require(n > Zero)
    n match {
      case Succ(p) => times_two_even(pow(Two, p))
    }
  }.ensuring(_ => isEven(pow(Two, n)))

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

  @opaque @inlineOnce
  def assoc_plus_minus_one(n: Nat, n2: Nat): Unit = {
    pow_positive(Two, n)
    commutative_plus(Two * n2, One)
    increasing_times(pow(Two, n), (Two * n2 + One))
    associative_plus_minus(One, pow(Two, n) * (Two * n2 + One), One)
  }.ensuring(_ =>
    One + (pow(Two, n) * (Two * n2 + One) - One) ==
    (One + pow(Two, n) * (Two * n2 + One)) - One
  )

  @opaque @inlineOnce
  def project_1_inverse(n1: Nat, n2: Nat): Unit = {
    decreases(n1)
    n1 match {
      case Succ(p1) =>
        {
          log2_and_remainder(Succ(pair(n1, n2)))                                  ==:|
                                                                            trivial |:
          log2_and_remainder(Succ(pow(Two, n1) * (Two * n2 + One) - One))         ==:|
                                                                            trivial |:
          log2_and_remainder(One + (pow(Two, n1) * (Two * n2 + One) - One))       ==:|
                                                        assoc_plus_minus_one(n1,n2) |:
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
                                                        assoc_plus_minus_one(p1,n2) |:
          log2_and_remainder(Two * Succ(pow(Two, p1) * (Two * n2 + One) - One))   ==:|
                                                                            trivial |:
          log2_and_remainder(Two * Succ(pair(p1, n2)))                            ==:|
                                            { times_two_even(Succ(pair(p1, n2)))
                                                       project_1_inverse(p1, n2)
                                      commutative_times(Two, Succ(pair(p1, n2)))
                                   multiplicative_inverse(Succ(pair(p1, n2)), Two) } |:
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
                                                             succ_times_two_odd(n2) |:
          ((Zero, Succ(Two * n2)): (Nat, Nat))                                    ==:|
                                                    commutative_plus(Two * n2, One) |:
          ((Zero, Two * n2 + One): (Nat, Nat))
        }.qed
    }
  }.ensuring(_ => log2_and_remainder(Succ(pair(n1, n2))) == (n1, (Two * n2 + One)))

  @opaque @inlineOnce
  def inverse_lemma(n1: Nat, n2: Nat): Unit = {
    val (p1, remainder) = log2_and_remainder(Succ(pair(n1, n2)))
    val p2 = (remainder - One) / Two

    {
      project(pair(n1, n2))                ==:| trivial                         |:
      (p1, p2)                             ==:| trivial                         |:
      (p1, (remainder - One) / Two)        ==:| project_1_inverse(n1, n2)       |:
      (n1, ((Two * n2 + One) - One) / Two) ==:| additive_inverse(Two * n2, One) |:
      (n1, (Two * n2) / Two)               ==:| commutative_times(Two, n2)      |:
      (n1, (n2 * Two) / Two)               ==:| multiplicative_inverse(n2, Two) |:
      (n1, n2)
    }.qed

  }.ensuring(_ => project(pair(n1, n2)) == (n1, n2))

  @opaque @inlineOnce
  def pair_unique(n1: Nat, n2: Nat, n3: Nat, n4: Nat): Unit = {
    if (pair(n1, n2) == pair(n3, n4)) {
      assert(project(pair(n1, n2)) == project(pair(n3, n4)))
      inverse_lemma(n1, n2)
      inverse_lemma(n3, n4)
      assert((n1, n2) == (n3, n4))
      ((n1, n2) == (n3, n4) ==:| trivial |: true).qed
    } else {
      assert((n1, n2) != (n3, n4))
      ((n1, n2) == (n3, n4) ==:| trivial |: false).qed
    }
  }.ensuring(_ => (pair(n1, n2) == pair(n3, n4)) == ((n1, n2) == (n3, n4)))
}
