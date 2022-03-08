Introduction
============

The Stainless verification framework aims to help developers build
verified Scala software. It encourages using a small set of core
Scala features and provides unique verification functionality.
In particular, Stainless can

* verify statically that your program conforms to a given
  specification and that it cannot crash at run-time

* provide useful counterexamples when an implementation does
  not satisfy its specification

* verify that your program will terminate on all inputs


Stainless and Scala
-------------------

Stainless attempts to strike a delicate balance between the
convenience of use on the one hand and the simplicity of
reasoning on the other hand. Stainless supports verification
of Scala programs by applying a succession of semantic-preserving
transformations to the :doc:`Pure Scala <purescala>` fragment until
it fits into the fragment supported by
`Inox <https://github.com/epfl-lara/inox>`_.
The Pure Scala fragment is at the core of
the functional programming paradigm and should sound familiar to
users of Scala, Haskell, ML, and fragments
present in interactive theorem provers such as Isabelle and Coq. Thus,
if you do not already know Scala, learning the Stainless subset should
be easier as it is a smaller language. Moreover, thanks to the use of
a Scala front end, Stainless supports implicits and ``for``
comprehensions (which also serve as a syntax for monads in Scala).
Stainless also comes with a simple library of useful data types, which
are designed to work well with automated reasoning and Stainless's
language fragment.

In addition to this pure fragment, Stainless supports certain
:doc:`imperative <imperative>` features.
Features thus introduced are handled by
a translation into Pure Scala concepts. They are often more
than just syntactic sugar, because some of them require
significant modification of the original program, such as
introducing additional parameters to a set of functions.  As
an intended aspect of its current design, Stainless's language
currently does not provide a default encoding of
e.g. concurrency with a shared mutable heap, though it might
support more manageable forms of concurrency in the future.

If you would like to use Stainless now, check the
:doc:`installation` section and follow :doc:`gettingstarted` and :doc:`Tutorial <tutorial>`.
To learn more about the functionality that Stainless provides, read on below.

Software Verification
---------------------

The Stainless program verifier collects a list of top-level functions,
and verifies the *validity* of their *contracts*. Essentially, for each function,
it will (try to) prove that the postcondition always holds, assuming a given
precondition does hold. A simple example:

.. code-block:: scala

  def factorial(n: BigInt): BigInt = {
    require(n >= 0)
    if(n == 0) {
      BigInt(1)
    } else {
      n * factorial(n - 1)
    }
  } ensuring(res => res >= 0)

Stainless generates a ``postcondition`` verification condition for the above
function, corresponding to the predicate parameter to the ``ensuring``
expression. It attempts to prove it using a combination of an internal
algorithm and external automated theorem proving. Stainless will return one of the
following:

* The postcondition is ``valid``. In that case, Stainless was able to prove that for **any**
  input to the function satisfying the precondition, the postcondition will always hold.
* The postcondition is ``invalid``. It means that Stainless disproved the postcondition and
  that there exists at least one input satisfying the precondition such that the
  postcondition does not hold. Stainless will always return a concrete counterexample, very
  useful when trying to understand why a function is not satisfying its contract.
* The postcondition is ``unknown``. It means Stainless is unable to prove or find a
  counterexample. It usually happens after a timeout or an internal error occurring in
  the external theorem prover.

Stainless will also verify for each call site that the precondition of the invoked
function cannot be violated.

Stainless supports verification of a significant part of the Scala language, described in
:doc:`purescala` and :doc:`imperative`.

Program Termination
-------------------

A "verified" function in stainless is guaranteed to never crash, however, it can
still lead to an infinite evaluation. Stainless therefore provides a termination
checker that complements the verification of safety properties.

For each function in the program, Stainless will try to automatically infer a
decreasing metric associated with this function to prove termination. The
termination checker will then report one of the following:

* The function ``terminates``. In this case, Stainless was able to prove that for
  all inputs (satisfying the function's precondition), evaluation of the function
  under those inputs is guaranteed to terminate.
* The function ``loops``. In this case, Stainless was able to construct an input
  to the function such that evaluation under that input will be looping.
* The function ``maybe loops``. In the case where recursive functions are passed
  around as first-class functions, Stainless will sometimes over-approximate the
  potential call sites and report loops that may never occur.
* Termination of the function is ``unknown``. In this case, Stainless was neither
  able to prove nor disprove termination of the relevant function. Automated
  termination proving is a *hard* problem and such cases are thus to be expected.

In cases where automated termination checking fails, Stainless provides the user
with the ability to manually specify a measure under which termination should
occur through the ``decreases`` construct. For example, the
`McCarthy 91 function <https://en.wikipedia.org/wiki/McCarthy_91_function>`_
can be shown terminating as follows:

.. code-block:: scala

  def M(n: BigInt): BigInt = {
    decreases(stainless.math.max(101 - n, 0))
    if (n > 100) n - 10 else M(M(n + 11))
  } ensuring (_ == (if (n > 100) n - 10 else BigInt(91)))


It is also possible to add a pre-condition (``require(...)``) *before* ``decreases``.

