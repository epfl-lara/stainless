.. _quantifiedproperties:

Quantified Properties
=====================

Stainless supports *explicit quantifiers* through the
``stainless.lang.Quantifiers`` library.  Thanks to the instantiation of
universal quantifiers by the SMT solver, it is possible to use quantifiers
in a rather systematic and controlled way.  This chapter explains how to
introduce and eliminate quantifiers following the rules of *natural
deduction*, and illustrates each rule with a Stainless example.

.. contents::
   :local:

Importing the Quantifier Library
--------------------------------

All examples below assume the following imports:

.. code-block:: scala

   import stainless.lang._
   import stainless.lang.Quantifiers.*
   import stainless.annotation.*
   import stainless.lang.StaticChecks.*
   import stainless.lang.*

The library provides the following key constructs:

- ``Forall(p)``: an opaque wrapper around the built-in ``forall``, used to
  state that predicate ``p`` holds for all values of the quantified type.
- ``ForallOf(p)(a)``: instantiates ``Forall(p)`` at a concrete value ``a``,
  yielding ``p(a)``.
- ``Exists(p)``: defined as ``!Forall(x => !p(x))``, states that some value
  satisfies ``p``.
- ``ExistsThe(w)(p)``: introduces an existential by providing a witness ``w``
  with ``p(w)``.
- ``pickWitness(p)``: given ``Exists(p)``, returns a witness satisfying ``p``.

There are also helpers for reasoning about negated quantifiers:

- ``notExists(p)``: from ``!Exists(p)`` derives ``Forall(x => !p(x))``.
- ``notForall(p)``: from ``!Forall(p)`` derives ``Exists(x => !p(x))``.
- ``notExistsNot(p)``: from ``!Exists(x => !p(x))`` derives ``Forall(p)``.


Propositional Natural Deduction
-------------------------------

Before discussing quantifiers, we review how Stainless handles the
propositional connectives ``&&``, ``||``, ``!``, and ``==>``.

Conjunction (``&&``)
~~~~~~~~~~~~~~~~~~~~

**Introduction.** If ``p`` and ``q`` are both true, then ``p && q`` is true.

.. code-block:: scala

   @ghost
   def conjIntro(p: Boolean, q: Boolean): Unit = {
     require(p)
     require(q)
     ()
   }.ensuring(_ => p && q)

**Elimination.** From ``p && q`` we can derive ``p`` (or ``q``).

.. code-block:: scala

   @ghost
   def conjElimLeft(p: Boolean, q: Boolean): Unit = {
     require(p && q)
     ()
   }.ensuring(_ => p)

   @ghost
   def conjElimRight(p: Boolean, q: Boolean): Unit = {
     require(p && q)
     ()
   }.ensuring(_ => q)

Disjunction (``||``)
~~~~~~~~~~~~~~~~~~~~

**Introduction.** From ``p`` alone, we can derive ``p || q``.

.. code-block:: scala

   @ghost
   def disjIntroLeft(p: Boolean, q: Boolean): Unit = {
     require(p)
     ()
   }.ensuring(_ => p || q)

**Elimination.** If ``p || q`` holds and both ``p ==> r`` and ``q ==> r``
hold, then ``r`` holds.

.. code-block:: scala

   @ghost
   def disjElim(p: Boolean, q: Boolean, r: Boolean): Unit = {
     require(p || q)
     require(p ==> r)
     require(q ==> r)
     ()
   }.ensuring(_ => r)

Negation (``!``)
~~~~~~~~~~~~~~~~

**Double Negation Elimination.** From ``!!p``, derive ``p``.

.. code-block:: scala

   @ghost
   def doubleNegElim(p: Boolean): Unit = {
     require(!(!p))
     ()
   }.ensuring(_ => p)

**Double Negation Introduction.** From ``p``, derive ``!!p``.

.. code-block:: scala

   @ghost
   def doubleNegIntro(p: Boolean): Unit = {
     require(p)
     ()
   }.ensuring(_ => !(!p))

Implication (``==>``)
~~~~~~~~~~~~~~~~~~~~~

**Modus Ponens.** From ``p ==> q`` and ``p``, derive ``q``.

.. code-block:: scala

   @ghost
   def modusPonens(p: Boolean, q: Boolean): Unit = {
     require(p ==> q)
     require(p)
     ()
   }.ensuring(_ => q)

**Modus Tollens.** From ``p ==> q`` and ``!q``, derive ``!p``.

.. code-block:: scala

   @ghost
   def modusTollens(p: Boolean, q: Boolean): Unit = {
     require(p ==> q)
     require(!q)
     ()
   }.ensuring(_ => !p)


Quantifier Rules
----------------

Universal Quantification (``Forall``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Introduction (∀I).** To prove ``Forall(p)``, one must show that ``p(x)``
holds for an *arbitrary* ``x``.  In Stainless this is done by writing a
function whose body proves ``p(x)`` for a universally quantified variable.
The built-in ``forall`` is Skolemized when it needs to be proven.

.. code-block:: scala

   @ghost
   def forallIntro: Unit = {
     assert(stainless.lang.forall((x: BigInt) => x + 0 == x))
   }

**Elimination (∀E).** Given ``Forall(p)``, derive ``p(a)`` for any concrete
``a`` by calling ``ForallOf(p)(a)``.

.. code-block:: scala

   @ghost
   def forallElim(p: BigInt => Boolean, a: BigInt): Unit = {
     require(Forall(p))
     ForallOf(p)(a)
   }.ensuring(_ => p(a))

Existential Quantification (``Exists``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Introduction (∃I).** To prove ``Exists(p)``, provide a *witness* ``w``
such that ``p(w)`` holds, then call ``ExistsThe(w)(p)``.

.. code-block:: scala

   @ghost
   def existsIntro: Unit = {
     val p = (x: BigInt) => x > 0 && x < 10
     val witness: BigInt = 5
     assert(p(witness))
     ExistsThe(witness)(p)
   }.ensuring(_ => Exists((x: BigInt) => x > 0 && x < 10))

**Elimination (∃E).** Given ``Exists(p)``, obtain a witness ``w``
satisfying ``p(w)`` by calling ``pickWitness(p)``.

.. code-block:: scala

   @ghost
   def existsElim(p: BigInt => Boolean): BigInt = {
     require(Exists(p))
     val w: BigInt = pickWitness[BigInt](p)
     assert(p(w))
     w
   }.ensuring(res => p(res))


Negated Quantifiers
-------------------

The following rules connect negation and quantification, mirroring the
classical equivalences.

**¬∃ → ∀¬**: From ``!Exists(p)``, derive ``Forall(x => !p(x))``.

.. code-block:: scala

   @ghost
   def notExistsToForallNot(p: BigInt => Boolean): Unit = {
     require(!Exists(p))
     notExists(p)
   }.ensuring(_ => Forall((x: BigInt) => !p(x)))

**¬∀ → ∃¬**: From ``!Forall(p)``, derive ``Exists(x => !p(x))``.

.. code-block:: scala

   @ghost
   def notForallToExistsNot(p: BigInt => Boolean): Unit = {
     require(!Forall(p))
     notForall(p)
   }.ensuring(_ => Exists((x: BigInt) => !p(x)))

**¬∃¬ → ∀**: From ``!Exists(x => !p(x))``, derive ``Forall(p)``.

.. code-block:: scala

   @ghost
   def notExistsNotToForall(p: BigInt => Boolean): Unit = {
     require(!Exists((x: BigInt) => !p(x)))
     notExistsNot(p)
   }.ensuring(_ => Forall(p))


Combined Examples
-----------------

The following examples show how to combine multiple rules in one proof.

**Conjunction of universals.** From ``Forall(p)`` and ``Forall(q)``,
derive that ``p(x) && q(x)`` holds for all ``x``.

.. code-block:: scala

   @ghost
   def forallConjunction(p: BigInt => Boolean, q: BigInt => Boolean): Unit = {
     require(Forall(p))
     require(Forall(q))
     unfold(Forall(p))
     unfold(Forall(q))
     assert(stainless.lang.forall((x: BigInt) => p(x) && q(x)))
   }

**Weakening an existential.** From ``Exists(p)``,
derive ``Exists(x => p(x) || q(x))``.

.. code-block:: scala

   @ghost
   def existsWeaken(p: BigInt => Boolean, q: BigInt => Boolean): Unit = {
     require(Exists(p))
     val w = pickWitness[BigInt](p)
     assert(p(w) || q(w))
     ExistsThe(w)((x: BigInt) => p(x) || q(x))
   }.ensuring(_ => Exists((x: BigInt) => p(x) || q(x)))

**Universal modus ponens.** From ``Forall(x => p(x) ==> q(x))`` and
``Forall(p)``, derive that ``q(x)`` holds for all ``x``.

.. code-block:: scala

   @ghost
   def forallModusPonens(p: BigInt => Boolean, q: BigInt => Boolean): Unit = {
     require(Forall((x: BigInt) => p(x) ==> q(x)))
     require(Forall(p))
     unfold(Forall((x: BigInt) => p(x) ==> q(x)))
     unfold(Forall(p))
     assert(stainless.lang.forall((x: BigInt) => q(x)))
   }

Summary
-------

The following table summarizes the rules and the corresponding Stainless
constructs:

.. list-table:: Natural Deduction Rules in Stainless
   :header-rows: 1
   :widths: 25 35 40

   * - Rule
     - Logical Statement
     - Stainless Construct
   * - ∧-Introduction
     - P, Q ⊢ P ∧ Q
     - ``p && q`` in postcondition
   * - ∧-Elimination
     - P ∧ Q ⊢ P
     - Extract from ``p && q`` precondition
   * - ∨-Introduction
     - P ⊢ P ∨ Q
     - ``p || q`` in postcondition
   * - ∨-Elimination
     - P ∨ Q, P→R, Q→R ⊢ R
     - Case analysis + implications
   * - ¬¬-Elimination
     - ¬¬P ⊢ P
     - Automatic by SMT solver
   * - →-Elimination
     - P→Q, P ⊢ Q
     - ``p ==> q`` + ``p`` in preconditions
   * - ∀-Introduction
     - ⊢ ∀x.P(x)
     - ``forall(x => P(x))`` / Skolemization
   * - ∀-Elimination
     - ∀x.P(x) ⊢ P(a)
     - ``ForallOf(p)(a)``
   * - ∃-Introduction
     - P(w) ⊢ ∃x.P(x)
     - ``ExistsThe(w)(p)``
   * - ∃-Elimination
     - ∃x.P(x) ⊢ P(w) for some w
     - ``pickWitness(p)``
   * - ¬∃ → ∀¬
     - ¬∃x.P(x) ⊢ ∀x.¬P(x)
     - ``notExists(p)``
   * - ¬∀ → ∃¬
     - ¬∀x.P(x) ⊢ ∃x.¬P(x)
     - ``notForall(p)``
   * - ¬∃¬ → ∀
     - ¬∃x.¬P(x) ⊢ ∀x.P(x)
     - ``notExistsNot(p)``

The complete set of test cases can be found in
`frontends/benchmarks/verification/valid/NaturalDeduction.scala
<https://github.com/epfl-lara/stainless/blob/master/frontends/benchmarks/verification/valid/NaturalDeduction.scala>`_.
