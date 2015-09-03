.. _verification:

Verification
============

Software verification aims at making software safer. In its typical use case,
it is a tool that takes as input the source code of a program with
specifications as annotations and attempt to prove --- or disprove --- their
validity.

One of the core module of Leon is a verifier for the subset of Scala described
in the sections :ref:`Pure Scala <purescala>` and :ref:`XLang <xlang>`. In this
section we describe the specification language that can be used to declare
properties of programs, as well as the safety properties automatically checked
by Leon. We also discuss how Leon can be used to prove mathematical theorems.

Verification conditions
-----------------------

Given an input program, Leon generates individual verification conditions
corresponding to different properties of the program. A program is correct if
all of the generated verification conditions are ``valid``. The validity of some
conditions depends on the validity of other conditions --- typically a
postcondition is ``valid`` assuming the precondition is ``valid``.

For each function, Leon attempts to verify its contract, if there is one. A
*contract* is the combination of a *precondition* and a *postcondition*. A
function meets its contract if for any input parameter that passes the
precondition, the postcondition holds after executing the function.
Preconditions and postconditions are annotations given by the user --- they are
the specifications and hence cannot be inferred by a tool and must be provided.

In addition to user-provided contracts, Leon will also generate a few safety
verification conditions of its own. It will check that all of the array
accesses are within proper bounds, and that pattern matching always covers all
possible cases, even given complex precondition. The latter is different from
the Scala compiler checks on pattern matching exhaustiveness, as Leon considers
information provided by (explicit or implicit) preconditions to the ``match``
expression.

Postconditions
**************

One core concept in verification is to check the contract of functions. The most
important part in a contract is the postcondition. The postcondition specifies
the behaviour of the function. It takes into account the precondition and only
asserts the property of the output when the input satisfies the precondition.

Formally, we consider a function with a single parameter (one can generalize
the following for any number of parameters):

.. code-block:: scala

   def f(x: A): B = {
     require(prec)
     body
   } ensuring(r => post)

where, :math:`\mbox{prec}(x)` is a Boolean expression with free variables
contained in :math:`\{ x \}`, :math:`\mbox{body}(x)` is a Boolean expression with
free variables contained in :math:`\{ x \}` and :math:`\mbox{post}(x, r)` is a
Boolean expression with free variables contained in :math:`\{ x, r \}`. The
types of :math:`x` and :math:`r` are respectively ``A`` and ``B``. We write
:math:`\mbox{expr}(a)` to mean the substitution in :math:`\mbox{expr}` of its
free variable by :math:`a`.

Leon attempts to prove the following theorem:

.. math::

  \forall x. \mbox{prec}(x) \implies \mbox{post}(x, \mbox{body}(x))

If Leon is able to prove the above theorem, it returns ``valid`` for the
function ``f``. This gives you a guarantee that the function ``f`` is correct
with respect to its contract.

However, if the theorem is not valid, Leon will return a counterexample to the
theorem. The negation of the theorem is:

.. math::

  \exists x. \mbox{prec}(x) \land \neg \mbox{post}(x, \mbox{body}(x))

and to prove the validity of the negation, Leon finds a witness :math:`x` --- a
counterexample --- such that the precondition is verified and the postcondition
is not.

The general problem of verification is undecidable for a Turing-complete
language, and the Leon language is Turing-complete. So Leon has to be
incomplete in some sense. Generally, Leon will eventually find a counterexample
if one exists. However, in practice some program structures require too many
unrollings and Leon is likely to timeout (or being out of memory) before
finding the counterexample.  When the postcondition is valid, it could also
happen that Leon keeps unrolling the program forever, without being able to
prove the correctness. We discuss the exact conditions for this in the
chapter on Leon's algorithms.

Preconditions
*************

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
call to :math:`\mbox{f}`. Formally, for each such call site, Leon will attempt
to prove the following theorem:

.. math::

   \forall x. \mbox{pc}(x) \implies \mbox{prec}(\mbox{e}(x))

Leon will generates one such theorem for each static call site of a function with
a precondition.

.. note::

   Leon only assumes an open program model, where any function could be called from
   outside of the given program. In particular, Leon will not derive a precondition
   to a function based on known information in the context of the calls, such as
   knowing that the function is always given positive parameters. Any information needed
   to prove the postcondition will have to be provide as part of the precondition
   of a function.

Loop invariants
***************

Leon supports annotations for loop invariants in :ref:`XLang <xlang>`. To
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

Leon will prove point (1) and (2) above. Together, and by induction, they imply
that point (3) holds as well.

Array access safety
*******************

Leon generates verification conditions for the safety of array accesses. For
each array variable, Leon carries along a symbolic information on its length.
This information is used to prove that each expression used as an index in the
array is strictly smaller than that length. The expression is also checked to
be positive.

Pattern matching exhaustiveness
*******************************

Leon verifies that pattern matching is exhaustive. The regular Scala compiler
only considers the types of expression involved in pattern matching, but Leon
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

But Leon will prove that the pattern matching is actually exhaustive,
relying on the given precondition.
