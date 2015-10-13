Introduction
============

The Leon system aims to help developers build verified Scala software.
It encourages using a small set of core Scala features, but provides
unique automation functionality. In particular, Leon can

* verify statically that your program confirms to a given
  specification and that it cannot crash at run-time

* repair a program for you to ensure that the above holds

* automatically execute and synthesize working functions
  from partial input/output specifications and test cases.

Leon and Scala
--------------

Leon attempts to strike a delicate balance between the convenience 
of use on the one hand and the simplicity of reasoning 
on the other hand. 
Leon primarily supports programs written in :ref:`Pure Scala <purescala>`, a purely
functional subset of Scala. 
This fragment is at the core of 
the functional programming paradigm and lies at the intersection
of functional languages such as Scala, Haskell, ML, and fragments present in interactive theorem provers such as Isabelle and Coq. Thus,
if you do not already know Scala, learning the Leon subset should
be easier as it is a smaller language.
The :ref:`Pure Scala <purescala>` features are at the core of the Leon
system. They are considered as primitives and get a personalized treatment in
the solving algorithms of Leon. 
Leon's algorithms can map this fragment into the first-order language
of SMT (satisfiability modulo theory) solvers, enabling
efficient automated reasoning. Moreover, thanks to the use of 
``scalac`` front end, Leon supports implicits and ``for`` 
comprehensions (which also serve as a syntax for monads in Scala).
Leon also comes with a simple library of useful data types, which are designed
to work well with automated reasoning and Leon's language fragment.

In addition to this pure fragment, Leon supports the
:ref:`XLang <xlang>` extension, which enables Leon to work
on a richer subset of Scala, including imperative features.
Features introduced by :ref:`XLang <xlang>` are handled by
translation into Pure Scala concepts. They are often more
than just syntactic sugar, because some of them require
significant modification of the original program, such as
introducing additional parameters to a set of functions.  As
an intended aspect of its current design, Leon's language
currently does not provide a default encoding of
e.g. concurrency with a shared mutable heap, though it might
support more manageable forms of concurrency in the future.
For practical reasons, Leon programs can also call out into
general Scala code, which needs to be used with care as it
is a form of "foreign function interface" into the general
world of Scala.

If you would like to use Leon now, check the :ref:`Getting Started <gettingstarted>`
section and try our :ref:`Tutorial <tutorial>`.
To learn more about the functionality that Leon provides, read on below.

Software Verification
---------------------

Leon started out as a program verifier for :ref:`Pure Scala <purescala>`. It
would collect a list of top level functions written in Pure Scala, and verifies
the *validity* of their *contracts*. Essentially, for each function, 
it would prove that the postcondition always hold, assuming a given precondition does
hold. A simple example:

.. code-block:: scala

   def factorial(n: Int): Int = {
     require(n >= 0)
     if(n == 0) {
       1
     } else {
       n * factorial(n - 1)
     }
   } ensuring(res => res >= 0)

Leon generates a ``postcondition`` verification condition for the above
function, corresponding to the predicate parameter to the ``ensuring``
expression. It attempts to prove it using a combination of an internal
algorithm and external automated theorem proving. Leon will return one of the
following:

* The postcondition is ``valid``. In that case, Leon was able to prove that for **any**
  input to the function satisfying the precondition, the postcondition will always hold.
* The postcondition is ``invalid``. It means that Leon disproved the postcondition and
  that there exists at least one input satisfying the precondition and such that the
  postcondition does not hold. Leon will always return a concrete counterexample, very
  useful when trying to understand why a function is not satisfying its contract.
* The postcondition is ``unknown``. It means Leon is unable to prove or find a counterexample.
  It usually happens after a timeout or an internal error occurring in the external 
  theorem prover. 

Leon will also verify for each call site that the precondition of the invoked
function cannot be violated.

Leon supports verification of a significant part of the Scala language, described in the
sections :ref:`Pure Scala <purescala>` and :ref:`XLang <xlang>`.




Program Synthesis
-----------------

As seen with verification, specifications provide an alternative and more
descriptive way of characterizing the behavior of a function.
Leon defines ways to use specifications instead of an actual implementation
within your programs:

* a ``choose`` construct that describes explicitly a value with a
  specification. For instance, one could synthesize a function inserting into a
  sorted list by:

.. code-block:: scala

  def insert1(in: List, v: BigInt) = {
    require(isSorted(in1))
    choose { (out: List) =>
      (content(out) == content(in1) ++ Set(v)) && isSorted(out)
    }
  }

* a hole (``???``) that can be placed anywhere in a specified function. Leon
  will fill it with values such that the overall specification is satisfied.
  This construct is especially useful when only a small part of the function
  is missing.

.. code-block:: scala

  def insert2(in: List, v: BigInt) = {
    require(isSorted(in1))
    in match {
      case Cons(h, t) =>
        if (h < v) {
          Cons(h, in)
        } else if (h == v) {
          in
        } else {
           ???[List]
        }
      case Nil =>
        Nil
    }
  } ensuring { out =>
    (content(out) == content(in1) ++ Set(v)) && isSorted(out)
  }


Given such programs, Leon can:

 1) Execute them: when the evaluator encounters a ``choose`` construct, it
 solves the constraint at runtime by invoking an SMT solver. This allows some
 form of constraint solving programming.

 2) Attempt to translate specifications to a traditional implementation by
 applying program synthesis. In our case, Leon will automatically synthesize
 the hole in ``insert2`` with ``Cons(h, insert2(v, t))``. This automated
 translation is described in further details in the section on :ref:`synthesis
 <Synthesis>`.



Program Repair
--------------

Leon can repair buggy :ref:`Pure Scala <purescala>` programs.
Given a specification and an erroneous implementation, Leon will
localize the cause of the bug and provide an alternative solution.
An example:

.. code-block:: scala

   def moddiv(a: Int, b: Int): (Int, Int) = {
     require(a >= 0 && b > 0);
     if (b > a) {
       (1, 0) // fixme: should be (a, 0)
     } else {
       val (r1, r2) = moddiv(a-b, b)
       (r1, r2+1)
     }
   } ensuring {
     res =>  b*res._2 + res._1 == a
   }

Invoking ``leon --repair --functions=moddiv`` will yield: ::

  ...
  [  Info  ] Found trusted solution!
  [  Info  ] ============================== Repair successful: ==============================
  [  Info  ] --------------------------------- Solution 1: ---------------------------------
  [  Info  ] (a, 0)
  [  Info  ] ================================= In context: =================================
  [  Info  ] --------------------------------- Solution 1: ---------------------------------
  [  Info  ] def moddiv(a : Int, b : Int): (Int, Int) = {
               require(a >= 0 && b > 0)
               if (b > a) {
                 (a, 0)
               } else {
                 val (r1, r2) = moddiv(a - b, b)
                 (r1, (r2 + 1))
               }
             } ensuring {
               (res : (Int, Int)) => (b * res._2 + res._1 == a)
             }

Repair assumes a small number of localized errors.
It first invokes a test-based fault localization algorithm,
and then a special synthesis procedure, which is partially guided
by the original erroneous implementation. For more information,
see the section on :ref:`Repair <repair>`.

