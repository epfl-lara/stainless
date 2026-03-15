.. _quantifiers:

Natural Deduction with Quantifiers
===================================

Stainless supports systematic reasoning with quantifiers through explicit
quantifier introduction and elimination, similar to natural deduction systems.
This chapter explains how to prove properties involving universal quantification
(``Forall``) and existential quantification (``Exists``), as well as how to
combine them with propositional logic operations.

Overview
--------

The ``stainless.lang.Quantifiers`` library provides opaque quantifiers that can
be explicitly manipulated in proofs. These differ from the built-in ``forall``
construct, which is automatically instantiated by the SMT solver. The explicit
quantifiers allow for more controlled reasoning following natural deduction
principles.

The key operations provided are:

* **Universal quantification**: ``Forall``, ``Forall2``, ``Forall3``, etc.
* **Universal instantiation**: ``ForallOf``, ``Forall2of``, ``Forall3of``, etc.
* **Existential quantification**: ``Exists``
* **Existential introduction**: ``ExistsThe``
* **Existential elimination**: ``pickWitness``
* **Quantifier negation**: ``notExists``, ``notExistsNot``, ``notForall``

Propositional Logic Foundations
--------------------------------

Before working with quantifiers, it's important to understand how propositional
logic works in Stainless. The basic operations are:

Conjunction (&&)
****************

Conjunction represents "and" in logical formulas. In natural deduction:

* **Introduction**: If you have both P and Q, you can conclude P && Q
* **Elimination**: From P && Q, you can derive either P or Q

Example:

.. code-block:: scala

   import stainless.lang.*

   def conjElim(p: Boolean, q: Boolean): Unit = {
     require(p && q)
     assert(p)  // Left elimination
     assert(q)  // Right elimination
   }.ensuring(_ => p && q)

Disjunction (||)
****************

Disjunction represents "or" in logical formulas:

* **Introduction**: From P, you can conclude P || Q (and vice versa)
* **Elimination**: If P || Q holds, and both P and Q separately imply R, then R holds

Example:

.. code-block:: scala

   def disjIntro(p: Boolean, q: Boolean): Unit = {
     require(p)
   }.ensuring(_ => p || q)  // We can introduce disjunction

   def disjElim(p: Boolean, q: Boolean, r: Boolean): Unit = {
     require(p || q)
     require(p ==> r)
     require(q ==> r)
   }.ensuring(_ => r)  // Case analysis

Negation (!)
************

Negation represents "not" in logical formulas. Key principles:

* **Double negation**: ``!!p`` is equivalent to ``p``
* **De Morgan's laws**: Transform negations of conjunctions/disjunctions

Example:

.. code-block:: scala

   def deMorgan1(p: Boolean, q: Boolean): Unit = {
     require(!(p && q))
   }.ensuring(_ => !p || !q)

   def deMorgan2(p: Boolean, q: Boolean): Unit = {
     require(!(p || q))
   }.ensuring(_ => !p && !q)

Universal Quantification (Forall)
----------------------------------

Universal quantification expresses that a property holds for all values of a type.
The ``Forall`` construct provides an opaque version of the built-in ``forall``
that requires explicit instantiation.

Basic Usage
***********

To use ``Forall``, you must:

1. Import from ``stainless.lang.Quantifiers``
2. Define a predicate (a function returning Boolean)
3. Use ``Forall`` to assert the predicate holds for all values

.. code-block:: scala

   import stainless.lang.Quantifiers.*

   def example(): Unit = {
     val p = (x: BigInt) => x >= 0 ==> x + 1 > 0
     require(Forall(p))
     // Now we know p holds for all x
   }

Forall Elimination (Universal Instantiation)
*********************************************

The key operation with universal quantifiers is **instantiation**: if we know
a property holds for all values, we can derive that it holds for any specific value.

This is done using ``ForallOf``:

.. code-block:: scala

   import stainless.lang.Quantifiers.*
   import stainless.lang.unfold

   def forallElim(a: BigInt): Unit = {
     val p = (x: BigInt) => x >= 0 ==> x + 1 > 0
     require(Forall(p))
     ForallOf(p)(a)  // Instantiate with specific value a
   }.ensuring(_ => a >= 0 ==> a + 1 > 0)

The ``ForallOf`` function:
* Requires ``Forall(p)`` to hold
* Takes a specific value ``a``
* Ensures ``p(a)`` holds after the call

Multi-arity Quantifiers
************************

For predicates with multiple arguments, use ``Forall2``, ``Forall3``, etc.:

.. code-block:: scala

   def forall2Example(a: BigInt, b: BigInt): Unit = {
     val p = (x: BigInt, y: BigInt) => x + y == y + x
     require(Forall2(p))
     Forall2of(p)(a, b)  // Instantiate with two values
   }.ensuring(_ => a + b == b + a)

Available multi-arity versions:
* ``Forall2`` and ``Forall2of`` for 2 parameters
* ``Forall3`` and ``Forall3of`` for 3 parameters
* ``Forall4`` and ``Forall4of`` for 4 parameters
* ``Forall5`` and ``Forall5of`` for 5 parameters

Forall Introduction
*******************

While there's no explicit ``Forall`` introduction function (it would require
proving the property for infinitely many values), you can establish ``Forall``
properties using the built-in ``forall`` in definitions:

.. code-block:: scala

   @ghost @opaque
   def allPositiveSquares: Boolean = Forall((x: BigInt) => x > 0 ==> x * x > 0)

The SMT solver will then attempt to prove this property.

Existential Quantification (Exists)
------------------------------------

Existential quantification expresses that there exists at least one value
satisfying a property. Unlike universal quantification, existential proofs
typically involve providing a specific witness.

Exists Introduction (Constructive Proof)
*****************************************

The most common way to prove an existential statement is to provide a specific
witness that satisfies the property using ``ExistsThe``:

.. code-block:: scala

   import stainless.lang.Quantifiers.*

   def existsIntro(): Unit = {
     val witness = BigInt(42)
     val p = (x: BigInt) => x > 0 && x % 2 == 0
     assert(p(witness))  // Verify witness satisfies property
     ExistsThe(witness)(p)  // Introduce existence
   }.ensuring(_ => Exists(p))

The ``ExistsThe`` function:
* Requires ``p(witness)`` to hold
* Ensures ``Exists(p)`` holds

This is the **constructive** way to prove existence: by exhibiting a concrete example.

Exists Elimination (Witness Extraction)
****************************************

If we know that ``Exists(p)`` holds, we can extract a witness using ``pickWitness``:

.. code-block:: scala

   def existsElim(): Unit = {
     val p = (x: BigInt) => x * x == 16
     require(Exists(p))
     val witness = pickWitness(p)
     assert(p(witness))  // witness satisfies p
   }

The ``pickWitness`` function:
* Requires ``Exists(p)`` to hold
* Returns some value ``w`` such that ``p(w)`` holds

Note that ``pickWitness`` is marked ``@extern``, meaning it's axiomatized rather
than computed. The specific witness returned is not determined.

Quantifier Negation (De Morgan's Laws)
---------------------------------------

Just as propositional logic has De Morgan's laws for negation of conjunctions
and disjunctions, quantifiers have corresponding rules for negation.

Negated Exists to Forall
*************************

The negation of an existential is a universal: ``!Exists(p)`` is equivalent to
``Forall(x => !p(x))``.

.. code-block:: scala

   import stainless.lang.Quantifiers.*

   def notExistsExample(): Unit = {
     val p = (x: BigInt) => x > 0 && x < 0  // Impossible
     require(!Exists(p))
     notExists(p)
     // Now we have: Forall((x: BigInt) => !p(x))
   }.ensuring(_ => Forall((x: BigInt) => !p(x)))

Negated Exists of Negation to Forall
*************************************

A double negation pattern: ``!Exists(x => !p(x))`` is equivalent to ``Forall(p)``.

.. code-block:: scala

   def notExistsNotExample(): Unit = {
     val p = (x: BigInt) => x >= x  // Always true
     require(!Exists((x: BigInt) => !p(x)))
     notExistsNot(p)
   }.ensuring(_ => Forall(p))

This states: "there does not exist an x for which p(x) is false" is the same as
"p(x) holds for all x".

Negated Forall to Exists
*************************

The negation of a universal is an existential: ``!Forall(p)`` is equivalent to
``Exists(x => !p(x))``.

.. code-block:: scala

   def notForallExample(): Unit = {
     val p = (x: BigInt) => x > 0  // Not true for all x
     require(!Forall(p))
     notForall(p)
   }.ensuring(_ => Exists((x: BigInt) => !p(x)))

This states: "not all x satisfy p" means "there exists an x that doesn't satisfy p".

Combining Quantifiers with Propositional Logic
-----------------------------------------------

The power of natural deduction comes from combining quantifiers with propositional
operators. Here are common patterns:

Forall with Conjunction
***********************

When a universal property is a conjunction, you can derive both parts separately:

.. code-block:: scala

   def forallConjunction(a: BigInt): Unit = {
     val p = (x: BigInt) => x > 0
     val q = (x: BigInt) => x < 100
     val pAndQ = (x: BigInt) => p(x) && q(x)
     require(Forall(pAndQ))
     ForallOf(pAndQ)(a)
     assert(p(a) && q(a))  // Both properties hold for a
   }

Conversely, if you have ``Forall(p)`` and ``Forall(q)``, then ``Forall(x => p(x) && q(x))`` holds.

Forall with Implication
***********************

A common pattern is universal quantification over implications:

.. code-block:: scala

   def forallImplication(x: BigInt): Unit = {
     val p = (n: BigInt) => n > 0 ==> n * 2 > 0
     require(Forall(p))
     require(x > 0)
     ForallOf(p)(x)
     assert(x * 2 > 0)  // Modus ponens after instantiation
   }

Exists with Disjunction
***********************

Existential proofs with disjunctions often involve case analysis:

.. code-block:: scala

   def existsDisjunction(n: BigInt): Unit = {
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

Nested Quantifiers
******************

Quantifiers can be nested, leading to more complex logical statements:

.. code-block:: scala

   def nestedQuantifiers(): Unit = {
     val p = (x: BigInt, y: BigInt) =>
       x + y == y + x && x * y == y * x
     require(Forall2(p))
     val a = BigInt(5)
     val b = BigInt(10)
     Forall2of(p)(a, b)
   }.ensuring(_ => {
     val a = BigInt(5)
     val b = BigInt(10)
     (a + b == b + a) && (a * b == b * a)
   })

Practical Examples
------------------

Example 1: Proving Properties of Functions
*******************************************

Suppose we want to prove that a function preserves certain properties:

.. code-block:: scala

   import stainless.lang.Quantifiers.*
   import stainless.annotation.*

   def increment(x: BigInt): BigInt = x + 1

   @ghost
   def incrementPreservesPositivity(n: BigInt): Unit = {
     val preserves = (x: BigInt) => x > 0 ==> increment(x) > 0
     require(Forall(preserves))
     require(n > 0)
     ForallOf(preserves)(n)
   }.ensuring(_ => increment(n) > 0)

Example 2: Constructing Existence Proofs
*****************************************

Finding a witness for an existential claim:

.. code-block:: scala

   @ghost
   def thereExistsEvenNumber(): Unit = {
     val witness = BigInt(42)
     val isEven = (x: BigInt) => x % 2 == 0 && x > 0
     assert(isEven(witness))
     ExistsThe(witness)(isEven)
   }.ensuring(_ => {
     val isEven = (x: BigInt) => x % 2 == 0 && x > 0
     Exists(isEven)
   })

Example 3: Using Quantifier Negation
*************************************

Transforming between quantifiers through negation:

.. code-block:: scala

   @ghost
   def noCounterexampleMeansForall(): Unit = {
     val p = (x: BigInt) => x * 0 == 0
     // Assume no counterexample exists
     require(!Exists((x: BigInt) => !p(x)))
     notExistsNot(p)
     // Now we can conclude p holds for all x
   }.ensuring(_ => Forall(p))

Example 4: Complex Case Analysis
*********************************

Combining multiple reasoning steps:

.. code-block:: scala

   @ghost
   def complexReasoning(n: BigInt): Unit = {
     val positive = (x: BigInt) => x > 0
     val negative = (x: BigInt) => x < 0

     require(n != 0)

     if n > 0 then
       ExistsThe(n)(positive)
     else
       assert(n < 0)
       ExistsThe(n)(negative)
   }.ensuring(_ => {
     val positive = (x: BigInt) => x > 0
     val negative = (x: BigInt) => x < 0
     Exists(positive) || Exists(negative)
   })

Relationship to Built-in Forall
--------------------------------

The opaque ``Forall`` quantifier is related to the built-in ``forall`` construct:

.. code-block:: scala

   @ghost @opaque
   def Forall[A](p: A => Boolean): Boolean = forall(p)

The key differences:

* **Built-in** ``forall``: Automatically instantiated by the SMT solver based on
  heuristics. Used in function contracts and inline assertions.

* **Opaque** ``Forall``: Requires explicit instantiation using ``ForallOf``.
  Provides more control over the proof structure.

The built-in ``forall`` is convenient but can be unpredictable. The opaque
``Forall`` gives you fine-grained control over when and how quantifiers are
instantiated, which is essential for complex proofs.

When proving that the result of a function satisfies a ``Forall`` property, the
built-in ``forall`` in the function body gets Skolemized (turned into a function
parameter that must be proven for arbitrary input).

Best Practices
--------------

1. **Use explicit quantifiers for complex proofs**: When automatic instantiation
   fails or is unpredictable, switch to ``Forall`` and ``ForallOf``.

2. **Provide witnesses for existential claims**: Use ``ExistsThe`` with concrete
   values rather than relying on the SMT solver to find witnesses.

3. **Leverage case analysis**: When proving disjunctions or existentials, use
   ``if-then-else`` to handle different cases explicitly.

4. **Break down complex properties**: Split conjunctions into separate lemmas,
   each focusing on one aspect of the property.

5. **Use helper lemmas**: For complex quantified formulas, prove intermediate
   results in separate lemmas.

6. **Combine propositional and quantified reasoning**: Don't forget about basic
   propositional logic rules when working with quantifiers.

Complete Working Example
-------------------------

Here's a complete example demonstrating multiple concepts:

.. code-block:: scala

   import stainless.lang.Quantifiers.*
   import stainless.annotation.*

   object QuantifierExample {

     def isEven(x: BigInt): Boolean = x % 2 == 0

     @ghost
     def evenPlusTwoIsEven(n: BigInt): Unit = {
       val prop = (x: BigInt) => isEven(x) ==> isEven(x + 2)
       require(Forall(prop))
       require(isEven(n))
       ForallOf(prop)(n)
     }.ensuring(_ => isEven(n + 2))

     @ghost
     def thereExistEvens(): Unit = {
       ExistsThe(BigInt(0))((x: BigInt) => isEven(x))
     }.ensuring(_ => Exists((x: BigInt) => isEven(x)))

     @ghost
     def notAllNumbersEven(): Unit = {
       val allEven = (x: BigInt) => isEven(x)
       require(!Forall(allEven))
       notForall(allEven)
       // Proven: there exists an odd number
     }.ensuring(_ => Exists((x: BigInt) => !isEven(x)))
   }

Further Reading
---------------

* See ``frontends/benchmarks/verification/valid/NaturalDeduction.scala`` for
  comprehensive test cases demonstrating all natural deduction rules.

* See ``frontends/benchmarks/verification/valid/ForallExistsTest.scala`` for
  additional examples of combining quantifiers.

* See ``frontends/library/stainless/lang/Quantifiers.scala`` for the complete
  API reference.

* The :doc:`neon` chapter covers inductive proofs and other proof techniques
  that complement natural deduction with quantifiers.
