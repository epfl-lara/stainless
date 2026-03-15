import stainless.lang._
import stainless.lang.Quantifiers.*
import stainless.annotation.*
import stainless.lang.StaticChecks.*
import stainless.lang.unfold

/**
 * Natural deduction rules for propositional connectives and quantifiers.
 *
 * This file demonstrates how to use Stainless to prove properties that
 * correspond to the standard introduction and elimination rules of
 * natural deduction for:
 *   - Conjunction (&&)
 *   - Disjunction (||)
 *   - Negation (!)
 *   - Implication (==>)
 *   - Universal quantification (Forall)
 *   - Existential quantification (Exists)
 *   - Negated quantifiers (!Forall, !Exists)
 */
object NaturalDeduction:

  // ===================================================================
  //  Conjunction (&&)
  // ===================================================================

  /** Conjunction Introduction: from P and Q, derive P && Q. */
  @ghost
  def conjIntro(p: Boolean, q: Boolean): Unit = {
    require(p)
    require(q)
    ()
  }.ensuring(_ => p && q)

  /** Conjunction Elimination Left: from P && Q, derive P. */
  @ghost
  def conjElimLeft(p: Boolean, q: Boolean): Unit = {
    require(p && q)
    ()
  }.ensuring(_ => p)

  /** Conjunction Elimination Right: from P && Q, derive Q. */
  @ghost
  def conjElimRight(p: Boolean, q: Boolean): Unit = {
    require(p && q)
    ()
  }.ensuring(_ => q)

  // ===================================================================
  //  Disjunction (||)
  // ===================================================================

  /** Disjunction Introduction Left: from P, derive P || Q. */
  @ghost
  def disjIntroLeft(p: Boolean, q: Boolean): Unit = {
    require(p)
    ()
  }.ensuring(_ => p || q)

  /** Disjunction Introduction Right: from Q, derive P || Q. */
  @ghost
  def disjIntroRight(p: Boolean, q: Boolean): Unit = {
    require(q)
    ()
  }.ensuring(_ => p || q)

  /** Disjunction Elimination: from P || Q, P ==> R, Q ==> R, derive R. */
  @ghost
  def disjElim(p: Boolean, q: Boolean, r: Boolean): Unit = {
    require(p || q)
    require(p ==> r)
    require(q ==> r)
    ()
  }.ensuring(_ => r)

  // ===================================================================
  //  Negation (!)
  // ===================================================================

  /** Double Negation Elimination: from !!P, derive P. */
  @ghost
  def doubleNegElim(p: Boolean): Unit = {
    require(!(!p))
    ()
  }.ensuring(_ => p)

  /** Double Negation Introduction: from P, derive !!P. */
  @ghost
  def doubleNegIntro(p: Boolean): Unit = {
    require(p)
    ()
  }.ensuring(_ => !(!p))

  // ===================================================================
  //  Implication (==>)
  // ===================================================================

  /** Modus Ponens: from P ==> Q and P, derive Q. */
  @ghost
  def modusPonens(p: Boolean, q: Boolean): Unit = {
    require(p ==> q)
    require(p)
    ()
  }.ensuring(_ => q)

  /** Modus Tollens: from P ==> Q and !Q, derive !P. */
  @ghost
  def modusTollens(p: Boolean, q: Boolean): Unit = {
    require(p ==> q)
    require(!q)
    ()
  }.ensuring(_ => !p)

  /** Hypothetical Syllogism: from P ==> Q and Q ==> R, derive P ==> R. */
  @ghost
  def hypotheticalSyllogism(p: Boolean, q: Boolean, r: Boolean): Unit = {
    require(p ==> q)
    require(q ==> r)
    ()
  }.ensuring(_ => p ==> r)

  // ===================================================================
  //  Universal Quantification (Forall)
  // ===================================================================

  /**
   * Forall Introduction: to prove Forall(p), prove that p(x) holds
   * for an arbitrary x. In Stainless, this is done by writing a
   * function that takes an arbitrary x and proves p(x) in its body,
   * then using the fact that the function ensures p(x) for all inputs.
   *
   * Here, we prove: Forall(x => x + 0 == x) for BigInt.
   */
  @ghost
  def forallIntro: Unit = {
    // The built-in forall is proved by Skolemization: Stainless proves p(x)
    // for an arbitrary x by considering a universally quantified variable.
    assert(stainless.lang.forall((x: BigInt) => x + 0 == x))
  }

  /**
   * Forall Elimination: given Forall(p), derive p(a) for a specific a.
   * This uses ForallOf to instantiate the universal quantifier.
   */
  @ghost
  def forallElim(p: BigInt => Boolean, a: BigInt): Unit = {
    require(Forall(p))
    ForallOf(p)(a)
  }.ensuring(_ => p(a))

  /**
   * Forall Elimination example with a concrete property:
   * Given that all integers satisfy x * 1 == x, derive that 42 * 1 == 42.
   */
  @ghost
  def forallElimExample: Unit = {
    val p = (x: BigInt) => x * 1 == x
    assert(stainless.lang.forall(p))
    // The above already lets the solver derive p(42)
    assert(p(42))
  }

  // ===================================================================
  //  Existential Quantification (Exists)
  // ===================================================================

  /**
   * Exists Introduction: to prove Exists(p), provide a witness w
   * such that p(w) holds, then use ExistsThe.
   *
   * Here, we prove: there exists an x such that x > 0 && x < 10.
   */
  @ghost
  def existsIntro: Unit = {
    val p = (x: BigInt) => x > 0 && x < 10
    val witness: BigInt = 5
    assert(p(witness))
    ExistsThe(witness)(p)
  }.ensuring(_ => Exists((x: BigInt) => x > 0 && x < 10))

  /**
   * Exists Elimination: given Exists(p), obtain a witness w with p(w).
   * Uses pickWitness to extract the witness.
   */
  @ghost
  def existsElim(p: BigInt => Boolean): BigInt = {
    require(Exists(p))
    val w: BigInt = pickWitness(p)
    assert(p(w))
    w
  }.ensuring(res => p(res))

  // ===================================================================
  //  Negated Quantifiers
  // ===================================================================

  /**
   * Not-Exists to Forall-Not: if !Exists(p), then Forall(x => !p(x)).
   * Uses the notExists helper from Quantifiers.
   */
  @ghost
  def notExistsToForallNot(p: BigInt => Boolean): Unit = {
    require(!Exists(p))
    notExists(p)
  }.ensuring(_ => Forall((x: BigInt) => !p(x)))

  /**
   * Not-Forall to Exists-Not: if !Forall(p), then Exists(x => !p(x)).
   * Uses the notForall helper from Quantifiers.
   */
  @ghost
  def notForallToExistsNot(p: BigInt => Boolean): Unit = {
    require(!Forall(p))
    notForall(p)
  }.ensuring(_ => Exists((x: BigInt) => !p(x)))

  /**
   * Not-Exists-Not to Forall: if !Exists(x => !p(x)), then Forall(p).
   * Uses the notExistsNot helper from Quantifiers.
   */
  @ghost
  def notExistsNotToForall(p: BigInt => Boolean): Unit = {
    require(!Exists((x: BigInt) => !p(x)))
    notExistsNot(p)
  }.ensuring(_ => Forall(p))

  // ===================================================================
  //  Combined Examples
  // ===================================================================

  /**
   * Example: from Forall(p) && Forall(q), derive Forall(x => p(x) && q(x)).
   * Combines forall elimination and conjunction introduction.
   */
  @ghost
  def forallConjunction(p: BigInt => Boolean, q: BigInt => Boolean): Unit = {
    require(Forall(p))
    require(Forall(q))
    // The built-in forall handles this via instantiation:
    // Stainless unfolds both Forall(p) and Forall(q) and uses the SMT solver.
    unfold(Forall(p))
    unfold(Forall(q))
    assert(stainless.lang.forall((x: BigInt) => p(x) && q(x)))
  }

  /**
   * Example: from Exists(p) derive Exists(x => p(x) || q(x)).
   * Combines existential elimination and disjunction introduction.
   */
  @ghost
  def existsWeaken(p: BigInt => Boolean, q: BigInt => Boolean): Unit = {
    require(Exists(p))
    val w = pickWitness(p)
    // w satisfies p, so it satisfies p || q
    assert(p(w) || q(w))
    ExistsThe(w)((x: BigInt) => p(x) || q(x))
  }.ensuring(_ => Exists((x: BigInt) => p(x) || q(x)))

  /**
   * Example: from Forall(x => p(x) ==> q(x)) and Forall(p), derive Forall(q).
   * Combines forall elimination with modus ponens.
   */
  @ghost
  def forallModusPonens(p: BigInt => Boolean, q: BigInt => Boolean): Unit = {
    require(Forall((x: BigInt) => p(x) ==> q(x)))
    require(Forall(p))
    unfold(Forall((x: BigInt) => p(x) ==> q(x)))
    unfold(Forall(p))
    assert(stainless.lang.forall((x: BigInt) => q(x)))
  }

end NaturalDeduction
