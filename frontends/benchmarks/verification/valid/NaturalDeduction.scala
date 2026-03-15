import stainless.lang.Quantifiers.*
import stainless.annotation.*
import stainless.lang.StaticChecks.*
import stainless.lang.unfold

/**
 * Comprehensive test cases demonstrating natural deduction in Stainless.
 *
 * This file demonstrates how to use natural deduction rules for:
 * 1. Propositional operations: conjunction (&&), disjunction (||), negation (!)
 * 2. Quantifiers: universal (Forall) and existential (Exists)
 *
 * These patterns can be used as templates for formal proofs in Stainless.
 */
object NaturalDeduction:

  // ============================================================================
  // PROPOSITIONAL LOGIC: CONJUNCTION (&&)
  // ============================================================================

  /**
   * Conjunction Introduction: If P and Q are both true, then P && Q is true.
   */
  @ghost
  def conjIntro(p: Boolean, q: Boolean): Unit = {
    require(p && q)
  }.ensuring(_ => p && q)

  /**
   * Conjunction Elimination (Left): From P && Q, we can derive P.
   */
  @ghost
  def conjElimLeft(p: Boolean, q: Boolean): Unit = {
    require(p && q)
    assert(p)
  }.ensuring(_ => p)

  /**
   * Conjunction Elimination (Right): From P && Q, we can derive Q.
   */
  @ghost
  def conjElimRight(p: Boolean, q: Boolean): Unit = {
    require(p && q)
    assert(q)
  }.ensuring(_ => q)

  /**
   * Conjunction Commutativity: P && Q implies Q && P.
   */
  @ghost
  def conjComm(p: Boolean, q: Boolean): Unit = {
    require(p && q)
  }.ensuring(_ => q && p)

  /**
   * Conjunction Associativity: (P && Q) && R is equivalent to P && (Q && R).
   */
  @ghost
  def conjAssoc(p: Boolean, q: Boolean, r: Boolean): Unit = {
    require((p && q) && r)
  }.ensuring(_ => p && (q && r))

  // ============================================================================
  // PROPOSITIONAL LOGIC: DISJUNCTION (||)
  // ============================================================================

  /**
   * Disjunction Introduction (Left): From P, we can derive P || Q.
   */
  @ghost
  def disjIntroLeft(p: Boolean, q: Boolean): Unit = {
    require(p)
  }.ensuring(_ => p || q)

  /**
   * Disjunction Introduction (Right): From Q, we can derive P || Q.
   */
  @ghost
  def disjIntroRight(p: Boolean, q: Boolean): Unit = {
    require(q)
  }.ensuring(_ => p || q)

  /**
   * Disjunction Elimination (Case Analysis):
   * If P || Q holds, and both P and Q separately imply R, then R holds.
   */
  @ghost
  def disjElim(p: Boolean, q: Boolean, r: Boolean): Unit = {
    require(p || q)
    require(p ==> r)
    require(q ==> r)
  }.ensuring(_ => r)

  /**
   * Disjunction Commutativity: P || Q implies Q || P.
   */
  @ghost
  def disjComm(p: Boolean, q: Boolean): Unit = {
    require(p || q)
  }.ensuring(_ => q || p)

  // ============================================================================
  // PROPOSITIONAL LOGIC: NEGATION (!)
  // ============================================================================

  /**
   * Double Negation Elimination: !!P implies P.
   */
  @ghost
  def doubleNegElim(p: Boolean): Unit = {
    require(!!p)
  }.ensuring(_ => p)

  /**
   * De Morgan's Law 1: !(P && Q) is equivalent to !P || !Q.
   */
  @ghost
  def deMorgan1(p: Boolean, q: Boolean): Unit = {
    require(!(p && q))
  }.ensuring(_ => !p || !q)

  /**
   * De Morgan's Law 2: !(P || Q) is equivalent to !P && !Q.
   */
  @ghost
  def deMorgan2(p: Boolean, q: Boolean): Unit = {
    require(!(p || q))
  }.ensuring(_ => !p && !q)

  /**
   * Contradiction: From P and !P, we can derive anything (ex falso quodlibet).
   */
  @ghost
  def contradiction(p: Boolean, q: Boolean): Unit = {
    require(p && !p)
  }.ensuring(_ => q)

  // ============================================================================
  // PROPOSITIONAL LOGIC: IMPLICATION (==>)
  // ============================================================================

  /**
   * Modus Ponens: From P and P ==> Q, we can derive Q.
   */
  @ghost
  def modusPonens(p: Boolean, q: Boolean): Unit = {
    require(p)
    require(p ==> q)
  }.ensuring(_ => q)

  /**
   * Modus Tollens: From !Q and P ==> Q, we can derive !P.
   */
  @ghost
  def modusTollens(p: Boolean, q: Boolean): Unit = {
    require(!q)
    require(p ==> q)
  }.ensuring(_ => !p)

  /**
   * Hypothetical Syllogism: From P ==> Q and Q ==> R, we can derive P ==> R.
   */
  @ghost
  def hypotheticalSyllogism(p: Boolean, q: Boolean, r: Boolean): Unit = {
    require(p ==> q)
    require(q ==> r)
    require(p)
  }.ensuring(_ => r)

  // ============================================================================
  // UNIVERSAL QUANTIFICATION: Forall Introduction and Elimination
  // ============================================================================

  /**
   * Forall Elimination (Universal Instantiation):
   * From Forall(P), we can derive P(a) for any specific value a.
   */
  @ghost
  def forallElim(a: BigInt): Unit = {
    val p = (x: BigInt) => x >= 0 ==> x + 1 > 0
    require(Forall(p))
    ForallOf(p)(a)  // Instantiate with specific value
  }.ensuring(_ => a >= 0 ==> a + 1 > 0)

  /**
   * Forall with Conjunction:
   * Forall(x => P(x) && Q(x)) implies Forall(x => P(x)) && Forall(x => Q(x)).
   */
  @ghost
  def forallConjunction(a: BigInt): Unit = {
    val p = (x: BigInt) => x > 0
    val q = (x: BigInt) => x < 100
    val pAndQ = (x: BigInt) => p(x) && q(x)
    require(Forall(pAndQ))
    ForallOf(pAndQ)(a)
    assert(p(a) && q(a))
  }.ensuring(_ => {
    val p = (x: BigInt) => x > 0
    val q = (x: BigInt) => x < 100
    val pAndQ = (x: BigInt) => p(x) && q(x)
    Forall(pAndQ) ==> (p(a) && q(a))
  })

  /**
   * Multi-arity Forall Elimination:
   * From Forall2((x,y) => P(x,y)), we can derive P(a,b) for specific values a, b.
   */
  @ghost
  def forall2Elim(a: BigInt, b: BigInt): Unit = {
    val p = (x: BigInt, y: BigInt) => x + y == y + x
    require(Forall2(p))
    Forall2of(p)(a, b)
  }.ensuring(_ => a + b == b + a)

  /**
   * Forall with Implication:
   * Demonstrates using Forall with implications for conditional properties.
   */
  @ghost
  def forallImplication(x: BigInt): Unit = {
    val p = (n: BigInt) => n > 0 ==> n * 2 > 0
    require(Forall(p))
    require(x > 0)
    ForallOf(p)(x)
  }.ensuring(_ => x * 2 > 0)

  // ============================================================================
  // EXISTENTIAL QUANTIFICATION: Exists Introduction and Elimination
  // ============================================================================

  /**
   * Exists Introduction (Existential Generalization):
   * From P(a) for some specific a, we can derive Exists(x => P(x)).
   */
  @ghost
  def existsIntro(): Unit = {
    val witness = BigInt(42)
    val p = (x: BigInt) => x > 0 && x % 2 == 0
    assert(p(witness))
    ExistsThe(witness)(p)
  }.ensuring(_ => {
    val p = (x: BigInt) => x > 0 && x % 2 == 0
    Exists(p)
  })

  /**
   * Exists Elimination (Witness Extraction):
   * From Exists(P), we can extract a witness that satisfies P.
   */
  @ghost
  def existsElim(): Unit = {
    val p = (x: BigInt) => x * x == 16
    require(Exists(p))
    val witness = pickWitness(p)
    assert(p(witness))
  }.ensuring(_ => {
    val p = (x: BigInt) => x * x == 16
    Exists(p) ==> true
  })

  /**
   * Exists with Conjunction:
   * Constructing an existence proof with multiple properties.
   */
  @ghost
  def existsConjunction(): Unit = {
    val witness = BigInt(10)
    val p = (x: BigInt) => x > 5 && x < 15 && x % 2 == 0
    assert(p(witness))
    ExistsThe(witness)(p)
  }.ensuring(_ => {
    val p = (x: BigInt) => x > 5 && x < 15 && x % 2 == 0
    Exists(p)
  })

  /**
   * Exists with Disjunction:
   * If Exists(x => P(x) || Q(x)), we can reason about the witness.
   */
  @ghost
  def existsDisjunction(): Unit = {
    val witness = BigInt(7)
    val p = (x: BigInt) => x % 2 == 1 || x % 2 == 0
    assert(p(witness))
    ExistsThe(witness)(p)
  }.ensuring(_ => {
    val p = (x: BigInt) => x % 2 == 1 || x % 2 == 0
    Exists(p)
  })

  // ============================================================================
  // QUANTIFIER NEGATION: De Morgan's Laws for Quantifiers
  // ============================================================================

  /**
   * Negated Exists to Forall:
   * !Exists(P) is equivalent to Forall(x => !P(x)).
   */
  @ghost
  def notExistsToForall(): Unit = {
    val p = (x: BigInt) => x > 0 && x < 0  // Contradiction: no such x exists
    require(!Exists(p))
    notExists(p)
    // Now we have Forall((x: BigInt) => !p(x))
  }.ensuring(_ => {
    val p = (x: BigInt) => x > 0 && x < 0
    Forall((x: BigInt) => !p(x))
  })

  /**
   * Negated Exists of Negation to Forall:
   * !Exists(x => !P(x)) is equivalent to Forall(P).
   */
  @ghost
  def notExistsNotToForall(): Unit = {
    val p = (x: BigInt) => x >= x  // Always true
    require(!Exists((x: BigInt) => !p(x)))
    notExistsNot(p)
  }.ensuring(_ => {
    val p = (x: BigInt) => x >= x
    Forall(p)
  })

  /**
   * Negated Forall to Exists:
   * !Forall(P) is equivalent to Exists(x => !P(x)).
   */
  @ghost
  def notForallToExists(): Unit = {
    val p = (x: BigInt) => x > 0  // Not true for all x (e.g., x = 0)
    require(!Forall(p))
    notForall(p)
  }.ensuring(_ => {
    val p = (x: BigInt) => x > 0
    Exists((x: BigInt) => !p(x))
  })

  // ============================================================================
  // COMBINED REASONING: Propositional Logic + Quantifiers
  // ============================================================================

  /**
   * Combining Forall with Conjunction (practical example):
   * Multiple universal properties combined.
   */
  @ghost
  def combinedForallConjunction(x: BigInt): Unit = {
    val p1 = (n: BigInt) => n >= 0 ==> n + 1 > n
    val p2 = (n: BigInt) => n >= 0 ==> n * 2 >= n
    require(Forall(p1) && Forall(p2))
    require(x >= 0)
    ForallOf(p1)(x)
    ForallOf(p2)(x)
  }.ensuring(_ => (x + 1 > x) && (x * 2 >= x))

  /**
   * Combining Exists with Disjunction (practical example):
   * Constructing existence proofs with alternative properties.
   */
  @ghost
  def combinedExistsDisjunction(n: BigInt): Unit = {
    val even = (x: BigInt) => x % 2 == 0
    val odd = (x: BigInt) => x % 2 == 1

    if n % 2 == 0 then
      ExistsThe(n)(even)
    else
      ExistsThe(n)(odd)
  }.ensuring(_ => {
    val even = (x: BigInt) => x % 2 == 0
    val odd = (x: BigInt) => x % 2 == 1
    Exists(even) || Exists(odd)
  })

  /**
   * Nested Quantifiers with Propositional Operators:
   * Demonstrating complex quantified formulas.
   */
  @ghost
  def nestedQuantifiers(): Unit = {
    val p = (x: BigInt, y: BigInt) => x + y == y + x && x * y == y * x
    require(Forall2(p))
    val a = BigInt(5)
    val b = BigInt(10)
    Forall2of(p)(a, b)
  }.ensuring(_ => {
    val a = BigInt(5)
    val b = BigInt(10)
    (a + b == b + a) && (a * b == b * a)
  })

  /**
   * Forall with Negation:
   * Universal quantification over negated properties.
   */
  @ghost
  def forallNegation(x: BigInt): Unit = {
    val p = (n: BigInt) => !(n > 0 && n < 0)  // No number is both positive and negative
    require(Forall(p))
    ForallOf(p)(x)
  }.ensuring(_ => !(x > 0 && x < 0))

  /**
   * Exists with Implication:
   * Existential quantification with conditional properties.
   */
  @ghost
  def existsImplication(): Unit = {
    val witness = BigInt(10)
    val p = (x: BigInt) => (x > 5) ==> (x * 2 > 10)
    assert(p(witness))
    ExistsThe(witness)(p)
  }.ensuring(_ => {
    val p = (x: BigInt) => (x > 5) ==> (x * 2 > 10)
    Exists(p)
  })

  /**
   * Case Analysis with Quantifiers:
   * Using disjunction elimination with existential properties.
   */
  @ghost
  def quantifierCaseAnalysis(n: BigInt): Unit = {
    require(n >= 0)
    val isEven = (x: BigInt) => x % 2 == 0
    val isOdd = (x: BigInt) => x % 2 == 1

    if n % 2 == 0 then
      ExistsThe(n)(isEven)
      assert(Exists(isEven))
    else
      ExistsThe(n)(isOdd)
      assert(Exists(isOdd))
  }.ensuring(_ => {
    val isEven = (x: BigInt) => x % 2 == 0
    val isOdd = (x: BigInt) => x % 2 == 1
    Exists(isEven) || Exists(isOdd)
  })

end NaturalDeduction
