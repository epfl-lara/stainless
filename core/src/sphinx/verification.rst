.. _verification:

Verification conditions
=======================

Software verification aims at making software safer. In its typical use case,
it is a tool that takes as input the source code of a program with
specifications as annotations and attempt to prove --- or disprove --- their
validity.

One of the core modules of Stainless is a verifier for the subset of Scala described
in the sections :doc:`purescala` and :doc:`imperative`. In this
section, we describe the specification language that can be used to declare
properties of programs, as well as the safety properties automatically checked
by Stainless. We also discuss how Stainless can be used to prove mathematical theorems.


Given an input program, Stainless generates individual verification conditions
corresponding to different properties of the program. A program is correct if
all of the generated verification conditions are ``valid``. The validity of some
conditions depends on the validity of other conditions --- typically a
postcondition is ``valid`` assuming the precondition is ``valid``.

For each function, Stainless attempts to verify its contract, if there is one. A
*contract* is the combination of a *precondition* and a *postcondition*. A
function meets its contract if, for any input parameter that passes the
precondition, the postcondition holds after executing the function.
Preconditions and postconditions are annotations given by the user --- they are
the specifications and hence cannot be inferred by a tool and must be provided.

In addition to user-provided contracts, Stainless will also generate a few safety
verification conditions of its own. It will check that all of the array
accesses are within proper bounds, and that pattern matching always covers all
possible cases, even given complex precondition. The latter is different from
the Scala compiler checks on pattern matching exhaustiveness, as Stainless considers
information provided by (explicit or implicit) preconditions to the ``match``
expression.

Postconditions
--------------

One core concept in verification is to check the contract of functions. The most
important part of a contract is the postcondition. The postcondition specifies
the behavior of the function. It takes into account the precondition and only
asserts the property of the output when the input satisfies the precondition.

Formally, we consider a function with a single parameter (one can generalize
the following for any number of parameters):

.. code-block:: scala

   def f(x: A): B = {
     require(prec)
     body
   } ensuring(r => post)

where, :math:`\mbox{prec}(x)` is a Boolean expression with free variables
contained in :math:`\{ x \}`, :math:`\mbox{body}(x)` is an expression with
free variables contained in :math:`\{ x \}` and :math:`\mbox{post}(x, r)` is a
Boolean expression with free variables contained in :math:`\{ x, r \}`. The
types of :math:`x` and :math:`r` are respectively ``A`` and ``B``. We write
:math:`\mbox{expr}(a)` to mean the substitution in :math:`\mbox{expr}` of its
free variable by :math:`a`.

Stainless attempts to prove the following theorem:

.. math::

  \forall x. \mbox{prec}(x) \implies \mbox{post}(x, \mbox{body}(x))

If Stainless is able to prove the above theorem, it returns ``valid`` for the
function ``f``. This gives you a guarantee that the function ``f`` is correct
with respect to its contract.

However, if the theorem is not valid, Stainless will return a counterexample to the
theorem. The negation of the theorem is:

.. math::

  \exists x. \mbox{prec}(x) \land \neg \mbox{post}(x, \mbox{body}(x))

and to prove the validity of the negation, Stainless finds a witness :math:`x` --- a
counterexample --- such that the precondition is verified and the postcondition
is not.

The general problem of verification is undecidable for a Turing-complete
language, and the Stainless language is Turing-complete. So Stainless has to be
incomplete in some sense. Generally, Stainless will eventually find a counterexample
if one exists. However, in practice, some program structures require too many
unrollings and Stainless is likely to timeout (or being out of memory) before
finding the counterexample.  When the postcondition is valid, it could also
happen that Stainless keeps unrolling the program forever, without being able to
prove the correctness. We discuss the exact conditions for this in the
chapter on Stainless's algorithms.

Preconditions
-------------

Preconditions are used as part of the contract of functions. They are a way to
restrict the input to only relevant inputs, without having to implement guards
and error handling in the functions themselves.

Preconditions are contracts that the call sites should respect, and thus are
not checked as part of verifying the function. Given the following definition:

.. code-block:: scala

   def f(x: A): B = {
     require(prec)
     body
   }


For each call site in the whole program (including in ``f`` itself):

.. code-block:: scala

   ...
   f(e)
   ...

where the expression :math:`\mbox{e}(x)` is an expression of type ``A`` with
free variables among :math:`\{ x \}`. Let us define the path condition on :math:`x`
at that program point as :math:`\mbox{pc}(x)`. The path condition is a formula that
summarizes the facts known about :math:`x` at that call site. A typical example is
when the call site is inside an if expression:

.. code-block:: scala

   if(x > 0)
     f(x)

The path condition on :math:`x` would include the fact that :math:`x > 0`. This
path condition is then used as a precondition of proving the validity of the
call to :math:`\mbox{f}`. Formally, for each such call site, Stainless will attempt
to prove the following theorem:

.. math::

   \forall x. \mbox{pc}(x) \implies \mbox{prec}(\mbox{e}(x))

Stainless will generate one such theorem for each static call site of a function with
a precondition.

.. note::

   Stainless only assumes an open program model, where any function could be called from
   outside of the given program. In particular, Stainless will not derive a precondition
   to a function based on known information in the context of the calls, such as
   knowing that the function is always given positive parameters. Any information needed
   to prove the postcondition will have to be provided as part of the precondition
   of a function.


Sharing bindings between specifications and function body
---------------------------------------------------------

The example `ValEnsuring <https://github.com/epfl-lara/stainless/blob/master/frontends/benchmarks/verification/valid/MicroTests/ValEnsuring.scala>`_
shows that Stainless supports multiple ``require``'s (in functions, but not for ADT invariants), and
shows how to share a `val` binding between precondition, postcondition, and function body.


Loop invariants
---------------

Stainless supports annotations for loop invariants in :doc:`imperative`. To
simplify the presentation we will assume a single variable :math:`x` is in
scope, but the definitions generalize to any number of variables. Given the
following program:

.. code-block:: scala

   (while(cond) {
     body
   }) invariant(inv)

where the Boolean expression :math:`\mbox{cond}(x)` is over the free variable
:math:`x` and the expression :math:`\mbox{body}(x, x')` relates the value of
:math:`x` when entering the loop to its updated value :math:`x'` on loop exit.
The expression :math:`\mbox{inv}(x)` is a Boolean formula over the free
variable :math:`x`.

A loop invariant must hold:
  (1) when the program enters the loop initially
  (2) after each completion of the body
  (3) right after exiting the loop (when the condition turns false)

Stainless will prove the points (1) and (2) above. Together, and by induction, they imply
that point (3) holds as well.

Stainless also supports ``noReturnInvariant`` (see `ReturnInWhile3 <https://github.com/epfl-lara/stainless/blob/master/frontends/benchmarks/imperative/valid/ReturnInWhile3.scala>`_) to describe loop invariants that are allowed to be broken
after a :doc:`return <imperative>` (can be combined with ``invariant``).

Decrease annotation in loops
----------------------------

One can also specify that the value of a given expression of numerical type decreases
at each loop iteration by adding a ``decreases`` measure within the loop body:

.. code-block:: scala

   while(cond) {
     decreases(expr)
     body
   }

Stainless will then emit a verification condition that checks whether the expression
is strictly positive and decreases at each iteration.

Array access safety
-------------------

Stainless generates verification conditions for the safety of array accesses. For
each array variable, Stainless carries along a symbolic information on its length.
This information is used to prove that each expression used as an index in the
array is strictly smaller than that length. The expression is also checked to
be positive.

ADT invariants
--------------

Stainless lets the user write ADT invariants with the ``require`` keyword.
Internally, such invariants are extracted as methods (named ``inv``). Whenever,
an ADT is constructed, and to make sure that the invariant is true, a
verification condition is generated with a call to the corresponding ``inv``
method.

The Stainless annotation ``@inlineInvariant`` used on an ADT or one of its
ancestors can be used to inline the call to ``inv`` in the verification
condition, as shown in the following example. This annotation is only
supported when ``--type-checker=true`` (which is the case by default).

.. code-block:: scala

  import stainless.annotation._

  object InlineInvariant {
    sealed abstract class A

    case class B(x: BigInt) extends A {
      require(x >= 50)
    }

    @inlineInvariant
    case class C(x: BigInt) extends A {
      require(x >= 50)
    }

    def f(): A = {
      B(100) // VC: inv(B(100))
      c(100) // VC: 100 >= 50 (call to `inv` was inlined)
    }
  }



Pattern matching exhaustiveness
-------------------------------

Stainless verifies that pattern matching is exhaustive. The regular Scala compiler
only considers the types of expression involved in pattern matching, but Stainless
will consider information such as precondition to formally prove the
exhaustiveness of pattern matching.

As an example, the following code should issue a warning with Scala:

.. code-block:: scala

   abstract class List
   case class Cons(head: Int, tail: List) extends List
   case object Nil extends List

   def getHead(l: List): Int = {
     require(!l.isInstanceOf[Nil])
     l match {
       case Cons(x, _) => x
     }
   }

But Stainless will prove that the pattern matching is actually exhaustive,
relying on the given precondition.
