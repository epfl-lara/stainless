.. _faq:

FAQ: (Frequently) Asked Questions
=================================

If you have a question, you may also post it at http://stackoverflow.com
(try `searching for the leon tag <http://stackoverflow.com/questions/tagged/leon?sort=newest>`_
or `the stainless tag <http://stackoverflow.com/questions/tagged/stainless?sort=newest>`_)
or contact one of the authors of this documentation.

Below we collect answers to some questions that came up.

How does Stainless compare to other verification tools?
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

One can compare Stainless to proof assistants such as
`Isabelle/HOL <https://isabelle.in.tum.de/>`_,
`Coq <https://coq.inria.fr/>`_,
`Lean <https://leanprover.github.io/>`_,
`HOL4 <https://hol-theorem-prover.org/>`_, or
`ACL2 <https://en.wikipedia.org/wiki/ACL2>`_ in terms of the complexity of some of the program properties it can prove, though it was originally conceived more as a program verifier, such as
`Dafny <https://github.com/epfl-lara/dafny>`_ or
`Viper <https://www.pm.inf.ethz.ch/research/viper.html>`_.
Stainless can be more automated when finding proofs of programs compared to proof assistants, and can also report counter-examples for invalid properties in many non-trivial cases, see counter-examples for bugs in benchmarks such as
`ConcRope.scala <static/invalid/BadConcRope.html>`_,
`ListOperations.scala <static/invalid/ListOperations.html>`_,
`Mean.scala <static/invalid/Mean.html>`_,
`PropositionalLogic.scala <static/invalid/PropositionalLogic.html>`_,
`AssociativityProperties.scala <static/invalid/AssociativityProperties.html>`_,
`InsertionSort.scala <static/invalid/InsertionSort.html>`_,
`more example reports <static/programs.html>`_, or check some of our
`regression tests <https://github.com/epfl-lara/stainless/tree/master/frontends/benchmarks/verification>`_.
On the other hand, proof assistants are much better at formalizing mathematics than Stainless, especially when it comes to libraries of formalized mathematics knowledge.

How does Stainless compare to fuzzing tools?
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Formal software verification finds proofs that programs work under all scenarios of interest. Formal verification tools help developers construct such proofs, automatically searching for proofs using theorem proving and constraint solving (using, e.g. SMT solvers), and static analysis to discover program invariants. When it succeeds, formal verification is guaranteed to identify all software errors, including, for example, security vulnerabilities or cases when the computation produces a wrong numerical or symbolic result. Because it involves building proofs, this approach may require knowledge of proofs by induction and substitution of equals for equals, typically covered in computer science undergraduate university education. The best approach to obtain formally verified software is to perform formal verification while software is developed. If we try to apply formal verification after software is already written, we should be prepared to invest at least the amount of effort needed to rewrite it.

Testing can establish the presence of errors, but not their absence. Basic forms of testing can be easy to deploy, because running a program on a given input is a minimum requirement for software, but such testing is extremely limited. Suppose that we wish to test whether a program running on a smartphone performs multiplication of two machine numbers correctly. If we could check one test per *nanosecond*, we would still need many billions of years to enumerate all cases! This also illustrates how minuscule of a region of space around a given test a fuzzer can ever explore, despite an amazing speed at which some these fuzzing tools work. Formal software verification can cover all these cases with a single proof because it uses algebraic properties that are independent of the size of the data that software manipulates.

To avoid enumeration, advanced testing methods such as symbolic execution embrace constraint solvers originally developed for formal verification. These techniques reduce to formal verification when programs have no loops or recursion; otherwise they end up sampling a small fraction of program executions, so they do not result in a proof. To cover more than just absence of crashes and vulnerabilities, testing also requires insights into the purpose of software, the environment in which the software needs to execute and the expected outputs for given inputs.

Does Stainless use SMT solvers?
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Stainless uses SMT solvers such as z3, CVC and Princess. The component that encodes formulas with executable higher-order functions into these solvers is Inox. Inox is designed to emit quantifier-free queries for these solvers, which increases its ability to generate counter-examples. The use of SMT solvers allows Stainless to achieve notable automation in reasoning about, for example, equality, case analysis, bitvectors, and algebraic data types.


What are the conditions required for Stainless to be applied to industry software?
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

It is best to deploy formal verification when starting to develop software. In this way, software and its specifications are developed hand in hand, much like one can define a class hierarchy and other types during the process of writing an object-oriented program. It is also possible to focus on one part of an existing software system and rewrite it in Stainless; such efforts have been shown to work in industry for software components in Scala, Java, and C.  Software that has well-defined modular structure with clear responsibility of different modules is a good candidate for verification because one can expect that specifications at module boundaries will be non-controversial. In terms of developer skills, good knowledge of discrete mathematics, such as proofs by induction and algebra will make developers more effective at verification.

Can I use Stainless with Java?
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Scala has excellent interoperability with Java, so external libraries can be used to build application where some parts are verified using Stainless. Stainless uses Scala syntax trees and does not support verification of Java itself. Whereas functional Scala works as a both specification and implementation language, Java does appear to be a good language for specifications, so much that Java verification tools in the past introduced their own logical notation that developers then must learn in addition to Java.

Can I use Stainless with Rust?
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Even though we had somewhat successful experiments translating Rust code into Stainless, we believe that, in the long term, it is more productive to use Scala as the starting point and generate low-level code. We are working on making this more practical in the future.

Proving properties of size
^^^^^^^^^^^^^^^^^^^^^^^^^^

I have defined a size function on my algebraic data type.

.. code-block:: scala

  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case object Nil extends List
  def size(l: List) : Int = (l match {
    case Nil => 0
    case Cons(_, t) => 1 + size(t)
  }) ensuring(_ >= 0)

Stainless neither proves nor gives a counterexample. Why?

**Answer:** You should consider using `BigInt`, which
denotes unbounded mathematical integers, instead of `Int`,
which denotes 32-bit integers. If you replace `Int` with
`BigInt` in the result type of `size`, the function should
verify. Note that algebraic data types can be arbitrarily
large, so, if the input list had the size `Int.MaxValue + 1`
(which is 2^32) then the addition `1 + size(t)` would wrap
around and produce `Int.MinValue` (that is, -2^31), so the
`ensuring` clause would not hold.

Compiling Stainless programs to bytecode
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

If you don't use special constructs such as ``choose`` or unbounded ``forall``, you
should be able to compile Stainless programs to `.class` using `scalac` and
execute them directly on the JVM, or integrate them as part as other
Scala-based projects. See Section ":ref:`running-code`".
