.. _neon:

Proving Theorems
================

Verifying the contract of a function is really proving a mathematical
theorem. Leon can be seen as a (mostly) automated theorem prover. It is
automated in the sense that once the property stated, Leon will proceed with searching
for a proof without any user interaction. In practice however, many theorems will be fairly
difficult to prove, and it is possible for the user to provide hints to Leon.

Hints typically take the form of simpler properties that combine in order to prove
more complicated ones. In the remaining subsections we provide code patterns and introduce
simple domain-specific language operators that can help in constructing complex Leon proofs.

A practical introduction to proofs
----------------------------------

When writing logical propositions such as preconditions or
postconditions in Leon, one is basically writing Boolean
predicates. They can be as simple as testing whether a list is empty
or not, to more complex combinations of properties.  Lemmas or
theorems are simply logical tautologies, that is, propositions that
always hold.  They can be expressed using Boolean-valued methods that
return ``true`` for all their inputs.

To make this more concrete, let's take a simple lemma as an
example [#example-dir]_. Here we want to prove that the append operation (``++``) on
lists preserves the content of the two lists being concatenated. This
proposition is relatively straightforward and Leon is able to verify
that it always holds.

.. code-block:: scala

    import leon.collection._ // for List
    import leon.lang._       // for holds

    object Example {
      def appendContent[A](l1: List[A], l2: List[A]): Boolean = {
        l1.content ++ l2.content == (l1 ++ l2).content
      }.holds
    }

Here we wrote ``.holds`` which is a method implicitly available on ``Boolean``
that ensure the returned value is ``true``. It is equivalent to writing
``ensuring { res => res }``.

Now let's look at another example that looks trivial but for which Leon
actually needs some help with the proof: we want to prove that adding ``Nil``
at the end of a list has no effect.

.. code-block:: scala

    import leon.collection._ // for List
    import leon.lang._       // for holds

    object Example {
      def rightUnitAppend[T](l1: List[T]): Boolean = {
        l1 ++ Nil() == l1
      }.holds
    }

If you try to verify this last example you'll face a delicate
situation: Leon runs indeterminately until it is either killed or
times out. But why does this happen?  The proposition doesn't seems
more complicated than ``appendContent``. Perhaps even more
surprisingly, Leon *is* able to verify the following:

.. code-block:: scala

    def leftUnitAppend[T](l1: List[T]): Boolean = {
      Nil() ++ l1 == l1
    }.holds

How is this possible?  The two propositions are completely symmetric!
The problem is that Leon doesn't know anything about lists, a priori.
It can only reason about lists thanks to their definition in terms of
the case classes ``Cons`` and ``Nil`` and associated methods such as
``++``.  In particular, Leon doesn't know that ``Nil`` represents the
empty list, and hence that appending it to some other list is a no-op.
What then, is the difference between the two examples above?  To
answer this question, we need to have a look at the definition of the
``++`` method:

.. code-block:: scala

  def ++(that: List[T]): List[T] = (this match {
    case Nil()       => that
    case Cons(x, xs) => Cons(x, xs ++ that)
  }) ensuring { res => /* ... */ }

Note that the implementation of ``++`` is recursive in its first
argument ``this`` but *not* in its second argument ``that``.  This is
why Leon was able to verify ``leftUnitAppend`` easily: it is true *by
definition*, i.e. ``Nil() ++ l1`` is actually defined to be ``l1``.
What about the symmetric case?  How is ``l1 ++ Nil()`` defined?  Well,
it depends on whether ``l1`` is the empty list or not.  So in order to
prove ``rightUnitAppend``, we need to proceed by case analysis.  The
resulting proof has a recursive (i.e. inductive) structure reminiscent
of the definition of ``++``:

.. code-block:: scala

    import leon.collection._ // for List
    import leon.lang._       // for holds
    import leon.proof._      // for because

    object Example {
      def rightUnitAppend[T](l1: List[T]): Boolean = {
        (l1 ++ Nil() == l1) because {
          l1 match {
            case Nil()       => true
            case Cons(x, xs) => rightUnitAppend(xs)
          }
        }
      }.holds
    }

With this new implementation of the ``rightUnitAppend`` lemma, Leon is capable
of verifying that it holds. If you look closely at it, you can distinguish three
parts:

1. the claim we want to prove ``l1 ++ Nil() == l1``;
2. ``because``, which is just some syntactic sugar for conjunction -- remember,
   every proposition is a Boolean formula;
3. and a recursion on ``l1`` that serves as a hint for Leon to perform
   induction.

The recursion is based here on pattern matching, which Leon will also check for
exhaustiveness.  It has essentially the same structure as
the implementation of ``++``: the base case is when ``l1`` is the empty list
and the inductive case is performed on ``Cons`` objects.


Techniques for proving non-trivial propositions
-----------------------------------------------

In the previous section we saw that "proof hints" can improve the odds
of Leon successfully verifying a given proposition.  In this section
we will have a closer look at what constitutes such a proof and
discuss a few techniques for writing them.

As mentioned earlier, propositions are represented by Boolean
expressions in Leon.  But how are proofs represented?  They are just
Boolean expressions as well [#props-not-types]_. The difference
between propositions and proofs is not their representation, but how
they are used by Leon.  Intuitively, a proof ``p: Boolean`` for a
proposition ``x: Boolean`` is an expression such that

 1. Leon is able to verify ``p``, and
 2. Leon is able to verify that ``p`` implies ``x``.

This is what we mean when we say that proofs are "hints".  Typically,
a proof ``p`` of a proposition ``x`` is a more complex-looking but
equivalent version of ``x``, i.e. an expression such that ``p == x``.
This might seem a bit counter-intuitive: why should it be easier for
Leon to verify an equivalent but more complex expression?  The answer
is that the more complex version may consist of sub-expressions that
more closely resemble the definitions of functions used in ``x``.  We
have already seen an example of this principle in the previous
section: let's have another look at the proof of ``rightUnitAppend``:

.. code-block:: scala

    def rightUnitAppend[T](l1: List[T]): Boolean = {
      val x = l1 ++ Nil() == l1
      val p = l1 match {
        case Nil()       => true
        case Cons(x, xs) => rightUnitAppend(xs)
      }
      x because p
    }.holds

Here, we have rewritten the example to make the distinction between
the proposition ``x`` and its proof ``p`` more explicit.  It's easy to
check that indeed ``x == p``, and hence the overall result of
``rightUnitAppend`` is equivalent to ``x`` (recall that ``because`` is
just an alias of ``&&``, so ``(x because p) == (x && x) == x``).
However, the proof term ``p`` closely resembles the definition of
``++`` and its sub-expressions are easier to verify for Leon than
``x`` itself.  The only non-trivial expression is the recursive call
to ``rightUnitAppend(xs)``, which serves as the inductive hypothesis.
We will discuss induction in more detail in Section
":ref:`induction`".


Divide and Conquer
******************

Before we delve into the details of particular proof techniques, it is
worth revisiting a guiding principle for writing proofs -- whether it
be in Leon, by hand, or using some other form of mechanized proof
checker -- namely to *modularize* proofs, i.e. to split the proofs of
complex propositions into manageable *sub-goals*.  This can be
achieved in various ways.

 * Use *helper lemmas* -- these are propositions that are lemmas on
   their own, i.e. they state and prove simple but self-contained
   propositions that can be reused elsewhere.  As such, they play a
   role akin to helper methods in normal programming, and indeed, are
   implemented in the same way, except that they carry a ``.holds``
   suffix.

 * Use *case analysis* to split complex propositions into simpler
   sub-cases.  This is especially helpful in the presence of
   recursion, where it leads to inductive proofs (see Section
   ":ref:`induction`").

 * Use *relational reasoning* to split complex relationships into
   conjunctions of elementary ones.  This often requires one to make
   use of relational properties such as transitivity (e.g. to break a
   single equation ``a == b`` into a chain of equations ``a == x1 &&
   x1 == x2 && ... && xN == b``), symmetry (e.g. to use a previously
   proven inequality ``a <= b`` where ``b >= a`` is expected),
   anti-symmetry (to unify variables), and so on (see Section
   ":ref:`rel-reasoning`").

 * Separate specification form implementation.  It is sometimes easier
   to prove the fact that a given function fulfills its specification
   as a separate lemma (although the proof techniques are roughly the
   same, see Section ":ref:`post-cond`").

 * Generalize (or specialize) propositions.  Sometimes, propositions
   are more easily proved in a stronger (or weaker) form and
   subsequently instantiated (or combined with other propositions) to
   yield a proof of the original proposition.

While it is good practice to factor common propositions into helper
lemmas, one sometimes wants to verify simple, specific sub-goals in a
proof without going through the trouble of introducing an additional
method.  This is especially true while one is exploring the branches
of a case analysis or wants to quickly check whether Leon is able to
prove a seemingly trivial statement automatically (we will see
examples of such situations in the coming sections).  For such cases,
one can use the ``check`` function from ``leon.proof``.  The ``check``
function behaves as the identity function on Booleans but additionally
assumes its argument in its precondition.  As a result, Leon will
check that ``x`` holds while verifying the call to ``check(x)``.
For example, when verifying the following function:

.. code-block:: scala

    import leon.proof.check

    def foo(x: BigInt): Boolean = {
      check(x >= 0 || x < 0) && check(x + 0 == 0)
    }

Leon will check (separately) that ``x >= 0 || x < 0`` and ``x + 0 ==
0`` hold for all ``x``, even though the function ``foo`` does not
specify any pre or postconditions, and report a counter example for
the second case::

    [  Info  ]  - Now considering 'precond. (call check(x >= 0 || x < 0))' VC for foo @40:5...
    [  Info  ]  => VALID
    [  Info  ]  - Now considering 'precond. (call check(x + 0 == 0))' VC for foo @40:31...
    [ Error  ]  => INVALID
    [ Error  ] Found counter-example:
    [ Error  ]   x -> 1

This is especially helpful when "debugging" proofs.


.. _induction:

Induction
*********

The vast majority of functional programs are written as functions over
:ref:`adts` (ADTs), and consequently, Leon comes with some special
support for verifying properties of ADTs.  Among other things, Leon
provides an annotation ``@induct``, which can be used to automatically
prove postconditions of recursive functions defined on ADTs by way of
*structural induction*.  We have already seen an example of such an
inductive property, namely ``rightUnitAppend``.  In fact, using
``@induct``, Leon is able to prove ``rightUnitAppend`` directly:

.. code-block:: scala

    import leon.annotation._  // for @induct

    @induct
    def rightUnitAppend[T](l1: List[T]): Boolean = {
      l1 ++ Nil() == l1
    }.holds

This is possible because the inductive step follows (more or less)
directly from the inductive hypothesis and Leon can verify the base
case automatically.  However, Leon may fail to verify more complex
functions with non-trivial base cases or inductive steps.  In such
cases, one may still try to provide proof hints by performing *manual
case analysis*.  Consider the following lemma about list reversal:

.. code-block:: scala

    import leon.collection._ // for List
    import leon.lang._       // for holds

    object Example {
      def reverseReverse[T](l: List[T]): Boolean = {
        l.reverse.reverse == l
      }.holds
    }

Leon is unable to verify ``reverseReverse`` even using ``@induct``.
So let's try and prove the lemma using manual case analysis.  We start
by adding an "unrolled" version of the proposition and inserting calls
to ``check`` in each branch of the resulting pattern match:

.. code-block:: scala

    def reverseReverse[T](l: List[T]): Boolean = {
      l.reverse.reverse == l because {
        l match {
          case Nil()       => check {  Nil[T]().reverse.reverse == Nil[T]()  }
          case Cons(x, xs) => check { (x :: xs).reverse.reverse == (x :: xs) }
        }
      }
    }.holds

Clearly, the two versions of the lemma are equivalent: all we did was
expand the proposition using a pattern match and add some calls to
``check`` (remember ``check`` acts as the identity function on its
argument).  Let's see what output Leon produces for the expanded
version::

    [  Info  ]  - Now considering 'postcondition' VC for reverseReverse @615:5...
    [Warning ]  => UNKNOWN
    [  Info  ]  - Now considering 'precond. (call check(List[T]().reverse().reverse() ...)' VC for reverseReverse @617:28...
    [  Info  ]  => VALID
    [  Info  ]  - Now considering 'precond. (call check({val x$27 = l.h; ...)' VC for reverseReverse @618:28...
    [Warning ]  => UNKNOWN
    [  Info  ]  - Now considering 'match exhaustiveness' VC for reverseReverse @616:7...
    [  Info  ]  => VALID

As expected, Leon failed to verify the expanded version.  However, we
get some additional information due to the extra pattern match and the
calls to ``check``.  In particular, Leon tells us that the match is
exhaustive, which means we covered all the cases in our case analysis
-- that's certainly a good start.  Leon was also able to automatically
verify the base case, so we can either leave the call to ``check`` as
is, or replace it by ``trivial``.  Unfortunately, Leon wasn't able to
verify the inductive step, something is missing.  Let's try to
manually reduce the inductive case and see where we get.

.. code-block:: scala

    def reverseReverse[T](l: List[T]): Boolean = {
      l.reverse.reverse == l because {
        l match {
          case Nil()       => trivial
          case Cons(x, xs) => check { (xs.reverse :+ x).reverse == (x :: xs) }
        }
      }
    }.holds

And now we're stuck.  We can't apply the inductive hypothesis here,
nor can we reduce the inductive case further, unless we perform
case analysis on ``xs``, which would grow the term further without
changing its shape.  To make any headway, we need to use an additional
property of ``reverse``, given by the following lemma (which Leon *is*
able to prove using ``@induct``):

.. code-block:: scala

    @induct
    def snocReverse[T](l: List[T], t: T): Boolean = {
      (l :+ t).reverse == t :: l.reverse
    }.holds

The lemma states that appending an element ``t`` to a list ``l`` and
reversing it is equivalent to first reversing ``l`` and then
prepending ``t``.  Using this lemma, we can write the proof of
``reverseReverse`` as

.. code-block:: scala

    def reverseReverse[T](l: List[T]): Boolean = {
      l.reverse.reverse == l because {
        l match {
          case Nil()       => trivial
          case Cons(x, xs) => check {
            (xs.reverse :+ x).reverse == x :: xs.reverse.reverse &&
            x :: xs.reverse.reverse   == (x :: xs)               because
              snocReverse(xs.reverse, x) && reverseReverse(xs)
          }
        }
      }
    }.holds

Leon is able to verify this version of the lemma.  Note that Leon
doesn't actually require us to include the two equations as they are
equivalent to the applications ``snocReverse(xs.reverse, x)`` and
``reverseReverse(xs)``.  Similarly, the call to ``check`` is somewhat
redundant now that Leon is able to verify the entire proof.  We could
thus "simplify" the above to

.. code-block:: scala

    def reverseReverse[T](l: List[T]): Boolean = {
      l.reverse.reverse == l because {
        l match {
          case Nil()       => trivial
          case Cons(x, xs) => snocReverse(xs.reverse, x) && reverseReverse(xs)
        }
      }
    }.holds

However, the previous version is arguably more readable for a human
being, and therefore preferable.  In Section ":ref:`rel-reasoning`" we
will see how readability can be improved even further through the use
of a DSL for equational reasoning.

So far, we have only considered structurally inductive proofs.
However, Leon is also able to verify proofs using *natural induction*
-- the form of induction that is perhaps more familiar to most
readers.  Consider the following definition of the exponential
function :math:`exp(x, y) = x^y` over integers:

.. code-block:: scala

    def exp(x: BigInt, y: BigInt): BigInt = {
      require(y >= 0)
      if      (x == 0) 0
      else if (y == 0) 1
      else             x * exp(x, y - 1)
    }

The function ``exp`` is again defined recursively, but this time using
``if`` statements rather than pattern matching.  Let's try and prove
some properties of this function using natural induction.  One such
property is that for any pair of positive numbers :math:`x, y \geq 0`,
the exponential :math:`x^y` is again a positive number.

.. code-block:: scala

    def positive(x: BigInt, y: BigInt): Boolean = {
      require(y >= 0 && x >= 0)
      exp(x, y) >= 0
    }

Since Leon doesn't know anything about exponentials, it isn't able to
verify the lemma without hints.  As with the previous example, we
start writing our inductive proof by expanding the top-level ``if``
statement in the definition of ``exp``.

.. code-block:: scala

    def positive(x: BigInt, y: BigInt): Boolean = {
      require(y >= 0 && x >= 0)
      exp(x, y) >= 0 because {
        if      (x == 0) check { exp(x, y) >= 0 }  // <-- valid
        else if (y == 0) check { exp(x, y) >= 0 }  // <-- valid
        else             check { exp(x, y) >= 0 }  // <-- unknown
      }
    }.holds

Leon was able to verify the first two (base) cases, but not the
inductive step, so let's continue unfolding ``exp`` for that case.

.. code-block:: scala

  def positive(x: BigInt, y: BigInt): Boolean = {
    require(y >= 0 && x >= 0)
    exp(x, y) >= 0 because {
      if      (x == 0) trivial
      else if (y == 0) trivial
      else             check { x * exp(x, y - 1) >= 0 }
    }
  }.holds

Although Leon still isn't able to verify the lemma, we now see a way
to prove the inductive step: ``x`` is positive (by the second
precondition) and so is ``exp(x, y - 1)`` (by the inductive
hypothesis).  Hence the product ``x * exp(x, y - 1)`` is again
positive.

.. code-block:: scala

  def positive(x: BigInt, y: BigInt): Boolean = {
    require(y >= 0 && x >= 0)
    exp(x, y) >= 0 because {
      if      (x == 0) trivial
      else if (y == 0) trivial
      else             check {
        x >= 0 && exp(x, y - 1) >= 0 because positive(x, y - 1)
      }
    }
  }.holds

With these hints, Leon is able to verify the proof.  Again, we could
shorten the proof by omitting inequalities that Leon can infer
directly, albeit at the expense of readability.

.. code-block:: scala

  def positiveShort(x: BigInt, y: BigInt): Boolean = {
    require(y >= 0 && x > 0)
    exp(x, y) >= 0 because {
      if      (x == 0) trivial
      else if (y == 0) trivial
      else             positiveShort(x, y - 1)
    }
  }.holds

We conclude the section with the inductive proof of another, somewhat
more interesting property of the exponential function, namely that
:math:`(x y)^z = x^z y^z`.

.. code-block:: scala

  def expMultCommute(x: BigInt, y: BigInt, z: BigInt): Boolean = {
    require(z >= 0)
    exp(x * y, z) == exp(x, z) * exp(y, z) because {
      if      (x == 0) trivial
      else if (y == 0) trivial
      else if (z == 0) trivial
      else             check {
        x * y * exp(x * y, z - 1) ==
          x * exp(x, z - 1) * y * exp(y, z - 1) because
          expMultCommute(x, y, z - 1)
      }
    }
  }.holds

.. _rel-reasoning:

Relational reasoning
********************

The majority of the example propositions we have seen so far related
some expression (e.g. ``l.reverse ++ Nil()`` or ``exp(x, y)``) to some
other expression (e.g. ``... == l1`` or ``... >= 0``).  This is
certainly a common case among the sorts of propositions about
functions and data structures one might wish to prove.  The proofs of
such propositions typically involve some form of *relational
reasoning*, i.e. reasoning involving properties (such as transitivity,
reflexivity or symmetry) of the relations in question.  Leon knows
about these properties for built-in relations such as ``==`` or orders
on numbers.  For user-defined relations, they first need to be
established as lemmas.  In this section, we discuss how to make
effective use of built-in relations, but the general principles extend
to their user-defined counterparts.

When working with simple structural equality, we can rely on the default ``==``
operator and Leon will happily understand when the reflexivity, symmetry and
transitivity properties apply and use them to conclude bigger proofs. Similarly,
when working on ``BigInt``, Leon knows about reflexivity, antisymmetry and
transitivity over ``>=`` or ``<=``, and also antireflexivity, antisymmetry
and transitivity of ``>`` and ``<``.

However, even for relatively simple proofs about ADTs, Leon needs
hints when combining, say equality, with user-defined operations, such
as ``++`` or ``reverse`` on lists.  For example, Leon is not able to
verify that the following holds for arbitrary pairs of lists ``l1``
and ``l2``:

.. code-block:: scala

    (l1 ++ l2).reverse == l2.reverse ++ l1.reverse

The hard part of giving hints to Leon is often to find them in the
first place.  Here we can apply a general principle on top of
structural induction (as discussed in the previous section): we start
from the left-hand side of an equation and build a chain of
intermediate equations to the right-hand side.  Using ``check``
statements we can identify where Leon times out and hence potentially
needs hints.

.. code-block:: scala

    def reverseAppend[T](l1: List[T], l2: List[T]): Boolean = {
      ( (l1 ++ l2).reverse == l2.reverse ++ l1.reverse ) because {
        l1 match {
          case Nil() =>
            /* 1 */ check { (Nil() ++ l2).reverse == l2.reverse                  } &&
            /* 2 */ check { l2.reverse            == l2.reverse ++ Nil()         } &&
            /* 3 */ check { l2.reverse ++ Nil()   == l2.reverse ++ Nil().reverse }
          case Cons(x, xs) =>
            /* 4 */ check { ((x :: xs) ++ l2).reverse       == (x :: (xs ++ l2)).reverse       } &&
            /* 5 */ check { (x :: (xs ++ l2)).reverse       == (xs ++ l2).reverse :+ x         } &&
            /* 6 */ check { (xs ++ l2).reverse :+ x         == (l2.reverse ++ xs.reverse) :+ x } &&
            /* 7 */ check { (l2.reverse ++ xs.reverse) :+ x == l2.reverse ++ (xs.reverse :+ x) } &&
            /* 8 */ check { l2.reverse ++ (xs.reverse :+ x) == l2.reverse ++ (x :: xs).reverse }
        }
      }
    }.holds

If we run the above code with a decent timeout, Leon reports four
*UNKNOWN* cases: the postcondition of the ``reverseAppend`` function itself and
checks number 2, 6 and 7.

 * Check #2 fails because, as we saw earlier, Leon is not capable of
   guessing the ``rightUnitAppend`` lemma by itself.  We fix this case
   by simply instantiating the lemma, i.e. by appending ``&&
   rightUnitAppend(l2.reverse)`` to the base case.

 * Check #6 fails because, at this point, we need to inject the
   induction hypothesis on ``xs`` and ``l2`` by adding ``&&
   reverseAppend(xs, l2)``.

 * Finally, check #7 fails for a similar reason as check #2: we need
   an additional "associativity" lemma to prove that ``(l1 ++ l2) :+ t
   == l1 ++ (l2 :+ t)`` holds for any ``l1``, ``l2`` and ``t``.  We
   call this lemma ``snocAfterAppend`` and leave it as an exercise for
   the reader.

Once we have a valid proof, we can try to optimize it for readability.
As it stands, the resulting code is rather verbose because both sides
of most equations are duplicated.  One option is to completely remove
the equations (they are implied by the instantiations of the lemmas)
and simply write

.. code-block:: scala

     def reverseAppend[T](l1: List[T], l2: List[T]): Boolean = {
       ( (l1 ++ l2).reverse == l2.reverse ++ l1.reverse ) because {
         l1 match {
           case Nil() =>
             rightUnitAppend(l2.reverse)
           case Cons(x, xs) =>
             reverseAppend(xs, l2) && snocAfterAppend(l2.reverse, xs.reverse, x)
         }
       }
     }.holds

Or we can employ the equational reasoning DSL provided by the
``leon.proofs`` package to remove the duplicate expressions and
interleave the equations with their associated proofs.  This has the
advantage of not losing information that is still useful for a human
being reading the proof later on:

.. code-block:: scala

    def reverseAppend[T](l1: List[T], l2: List[T]): Boolean = {
      ( (l1 ++ l2).reverse == l2.reverse ++ l1.reverse ) because {
        l1 match {
          case Nil() => {
            (Nil() ++ l2).reverse         ==| trivial                     |
            l2.reverse                    ==| rightUnitAppend(l2.reverse) |
            l2.reverse ++ Nil()           ==| trivial                     |
            l2.reverse ++ Nil().reverse
          }.qed
          case Cons(x, xs) => {
            ((x :: xs) ++ l2).reverse         ==| trivial               |
            (x :: (xs ++ l2)).reverse         ==| trivial               |
            (xs ++ l2).reverse :+ x           ==| reverseAppend(xs, l2) |
            (l2.reverse ++ xs.reverse) :+ x   ==|
              snocAfterAppend(l2.reverse, xs.reverse, x)                |
            l2.reverse ++ (xs.reverse :+ x)   ==| trivial               |
            l2.reverse ++ (x :: xs).reverse
          }.qed
        }
      }
    }.holds

The idea is to group statements in a block
(``{ }``) and call ``qed`` on it. Then, instead of writing ``a == b && b == c
&& hint1 && hint2`` we write ``a ==| hint1 | b ==| hint2 | c``. And when no
additional hint is required, we can use ``trivial`` which simply stands for
``true``.

Additionally, by using this DSL, we get the same feedback granularity from Leon
as if we had used ``check`` statements. This way we can construct proofs based
on equality more easily and directly identify where hints are vital.

One shortcoming of the relational reasoning DSL is that it relies on
Leon's knowledge of the relational properties of the built-in
relations, and in particular those of equality.  Consequently is works
badly (if at all) with user-defined relations.  However, since the DSL
is defined as a library (in ``library/proof/package.scala``), it can
in principle be extended and modified to include specific user-defined
relations on a case-by-case basis.

.. TODO add a word about requirement in ctor (e.g. Rational)

.. TODO Footnote linking to Etienne's answer on SO.


Limits of the approach: HOFs, quantifiers and termination
*********************************************************

While the techniques discussed in this section are useful in general,
their applicability has of course its limitations in practice.  These
limitations are mostly due to Leon's limited support for certain
language constructs, such as higher-order functions (HOFs) or
quantifiers (which in turn is due, mostly, to the limited support of
the corresponding theories in the underlying SMT solvers).

Still, even using these "experimental" features, one manages to prove
some interesting propositions.  Here is another list example, which
relates the ``foldLeft``, ``foldRight`` and ``reverse`` operations
defined on lists and makes crucial use of HOFs:

.. code-block:: scala

    import leon.collection._
    import leon.lang._
    import leon.proof._

    def folds[A, B](xs: List[A], z: B, f: (B, A) => B): Boolean = {
      val f2 = (x: A, z: B) => f(z, x)
      xs.foldLeft(z)(f) == xs.reverse.foldRight(z)(f2) because {
        xs match {
          case Nil() => true
          case Cons(x, xs) => {
            (x :: xs).foldLeft(z)(f)              ==| trivial               |
            xs.foldLeft(f(z, x))(f)               ==| folds(xs, f(z, x), f) |
            xs.reverse.foldRight(f(z, x))(f2)     ==| trivial               |
            xs.reverse.foldRight(f2(x, z))(f2)    ==|
              snocFoldRight(xs.reverse, x, z, f2)                           |
            (xs.reverse :+ x).foldRight(z)(f2)    ==| trivial               |
            (x :: xs).reverse.foldRight(z)(f2)
          }.qed
        }
      }
    }.holds

A rather different, more general issue that arises when proving
propositions using Leon is related to *termination checking*.  When
verifying inductive proofs (and more generally the postconditions of
recursive methods), Leon assumes that the corresponding proofs are
*well-founded*, or equivalently, that the corresponding recursive
methods terminate on all inputs.  Yet Leon does not -- by default --
check that this is the case.  It is thus possible -- and indeed rather
easy -- to write bogus proofs (intentionally or accidentally) which
Leon recognizes as valid, but which are not well-founded.  Consider
the following lemma, which apparently establishes that all lists are
empty:

.. code-block:: scala

    import leon.collection._
    import leon.lang._
    import leon.proof._

    object NotWellFounded {

      // This proof is not well-founded.  Since Leon doesn't run the
      // termination checker by default, it will accept the proof as
      // valid.
      def allListsAreEmpty[T](xs: List[T]): Boolean = {
        xs.isEmpty because {
          xs match {
            case Nil()       => trivial
            case Cons(x, xs) => allListsAreEmpty(x :: xs)
          }
        }
      }.holds
    }

Leon has (experimental) support for termination checking, which can be
enabled using the ``--termination`` command line option to minimize
the risk of accidentally writing bogus proofs such as the one above.

.. TODO example: folds + future work (alt. version of folds)

.. _post-cond:

Techniques for proving non-trivial postconditions
-------------------------------------------------

When proving a mathematical lemma, the return type of the
corresponding function is most of
the time, if not always, ``Boolean``. For those proofs it is rather easy to
write a postcondition: using ``holds`` is generally enough.

But when it comes to writing postconditions for more general functions, such as
the addition on rational numbers, we are no longer dealing with ``Boolean`` so
we need a strategy to properly write ``ensuring`` statements.


Rationals: a simple example
***************************

Let's take rational numbers as an example: we define them as a case class with
two attributes, `n` for the numerator and `d` for the denominator. We also
define three simple properties on them: ``isRational``, ``isNonZero`` and
``isPositive``.

.. code-block:: scala

    case class Rational(n: BigInt, d: BigInt) {
      def isRational = d != 0
      def isPositive = isRational && (n * d >= 0)
      def isNonZero  = isRational && (n != 0)

      // ...
    }

And on top of that we want to support addition on ``Rational`` in a way that
the rationality and positiveness properties are correctly preserved:

.. code-block:: scala

    def +(that: Rational): Rational = {
      require(isRational && that.isRational)
      Rational(n * that.d + that.n * d, d * that.d)
    } ensuring { res =>
      res.isRational &&
      (this.isPositive == that.isPositive ==> res.isPositive == this.isPositive)
    }

In this simple case, things work nicely and we can write the
multiplication in a similar fashion:

.. code-block:: scala

    def *(that: Rational): Rational = {
      require(isRational && that.isRational)
      Rational(n * that.n, d * that.d)
    } ensuring { res =>
      res.isRational &&
      (res.isNonZero  == (this.isNonZero && that.isNonZero)) &&
      (res.isPositive == (!res.isNonZero || this.isPositive == that.isPositive))
    }


Measures: a slightly more complex example
*****************************************

Now let's look at a slightly more complex example: measures on
discrete probability spaces.  We represent such measures using a
``List``-like recursive data structure: a generic abstract class
``Meas[A]`` that has two subclasses, ``Empty[A]`` and ``Cons[A]``.
The constructor of the class ``Empty[A]`` takes no arguments; it
represents an "empty" measure that evaluates to 0 when applied to any
set of values of type ``A``.  The constructor of ``Cons[A]``, on the
other hand, takes three parameters: a value ``x``, its associated
weight ``w`` expressed as a ``Rational`` (since Leon doesn't quite yet
support real numbers out of the box), and another measure ``m`` on
``A``.  The value ``Cons(x, w, m)`` represents the measure obtained by
adding to ``m`` the "single-point" measure that evaluates to ``w`` at
``x`` and to 0 everywhere else.  We also define an ``isMeasure``
property -- similar to the ``isRational`` property presented above --
which recursively checks that all the weights in a measure are
positive rationals (note that all our measures have finite support).

.. code-block:: scala

    /** Measures on discrete probability spaces. */
    sealed abstract class Meas[A] {

      /** All weights must be positive. */
      def isMeasure: Boolean = this match {
        case Empty()       => true
        case Cons(x, w, m) => w.isPositive && m.isMeasure
      }

      // ...
    }

    /** The empty measure maps every subset of the space A to 0. */
    case class Empty[A]() extends Meas[A]

    /**
     * The 'Cons' measure adjoins an additional element 'x' of type 'A'
     * to an existing measure 'm' over 'A'.  Note that 'x' might already
     * be present in 'm'.
     */
    case class Cons[A](x: A, w: Rational, m: Meas[A]) extends Meas[A]


The defining operation on a measure ``m`` is its evaluation ``m(xs)``
(or equivalently ``m.apply(xs)``) on some set ``xs: Set[A]``, i.e. on a
subset of the "space" ``A``.  The value of ``m`` should be a positive
rational for any such set ``xs``, provided ``m.isMeasure`` holds.
This suggests ``_.isPositive`` as the postcondition for ``apply``,
but simply claiming that the result is positive is not enough for Leon
to verify this postcondition.

We can provide the necessary hint to Leon by performing structural
induction on ``this`` inside the postcondition as follows:

.. code-block:: scala

    /** Compute the value of this measure on a subset of the space 'A'. */
    def apply(xs: Set[A]): Rational = {
      require (isMeasure)
      this match {
        case Empty()       => Rational(0, 1)
        case Cons(x, w, m) => if (xs contains x) w + m(xs) else m(xs)
      }
    } ensuring { res =>
      res.isPositive because {
        this match {
          case Empty()       => trivial
          case Cons(x, w, m) => m(xs).isPositive
        }
      }
    }

Notice the similarity between the pattern match in the body of the
``apply`` function and that in the postcondition.  With this hint,
Leon is able to verify the postcondition.


A complex example: additivity of measures
-----------------------------------------

Using the principles and techniques discussed so far, one can prove
quite advanced propositions using Leon.  Returning to the
measure-theoretic example from the previous section, we would like to
prove that our implementation of measures is properly *additive*.
Formally, a measure :math:`\mu \colon A \to \mathbb{R}` on a countable
set :math:`A` must fulfill the following additivity property
[#dicrete-meas]_:

.. math::

   \forall A_1, A_2 \subseteq A . A_1 \cap A_2 = \emptyset \Rightarrow
   \mu(A_1 \cup A_2) = \mu(A_1) + \mu(A_2)

which we can express in Leon as

.. code-block:: scala

  def additivity[A](m: Meas[A], xs: Set[A], ys: Set[A]): Boolean = {
    require(m.isMeasure && (xs & ys).isEmpty)
    m(xs ++ ys) == m(xs) + m(ys)
  }.holds

We can prove this property using structural induction on the parameter
``m``, case analysis on the parameters ``xs`` and ``ys``, equational
reasoning, and properties of rational numbers (in the form of
user-defined lemmas) as well as sets (using Leon's built-in support).

.. code-block:: scala

  def additivity[A](m: Meas[A], xs: Set[A], ys: Set[A]): Boolean = {
    require(m.isMeasure && (xs & ys).isEmpty)
    m(xs ++ ys) == m(xs) + m(ys) because {
      m match {
        case Empty()       => trivial
        case Cons(x, w, n) => if (xs contains x) {
          w + n(xs ++ ys)     ==| additivity(n, xs, ys)        |
          w + (n(xs) + n(ys)) ==| plusAssoc(w, n(xs), n(ys))   |
          (w + n(xs)) + n(ys) ==| !(ys contains x)             |
          m(xs)       + m(ys)
        }.qed else if (ys contains x) {
          w + n(xs ++ ys)     ==| additivity(n, xs, ys)        |
          w + (n(xs) + n(ys)) ==| plusComm(w, (n(xs) + n(ys))) |
          (n(xs) + n(ys)) + w ==| plusAssoc(n(xs), n(ys), w)   |
          n(xs) + (n(ys) + w) ==| plusComm(n(ys), w)           |
          n(xs) + (w + n(ys)) ==| !(xs contains x)             |
          m(xs) + m(ys)
        }.qed else {
          n(xs ++ ys)         ==| additivity(n, xs, ys)        |
          n(xs) + n(ys)
        }.qed
      }
    }
  }.holds

The full proof (including the proofs of all helper lemmas) as well as
its generalization to *sub-additivity* can be found in the
``testcases/verification/proof/measure/`` directory of the Leon
distribution [#example-dir]_.


Quick Recap
-----------

Let's summarize what we've learned here. To write proofs efficiently,
it's good to keep the following in mind:

1. Always use a proper timeout and ask Leon for more information about
   what he tries to verify, e.g. ``--timeout=5 --debug=verification``.

2. Use ``@induct`` when working on structurally inductive proofs to
   get a more precise feedback from Leon: this will decompose the
   proof into a base case and an inductive case for the first argument
   of the function under consideration.

   If Leon isn't able to verify the proof using ``@induct``, try
   performing manual case analysis.

3. Modularize your proofs and verify *sub-goals*!

   - use plenty of helper lemmas;
   - use ``check`` abundantly;
   - if possible use the relational reasoning DSL presented above.

   This is especially handy when you can connect the two sides of a relational
   claim with sub-statements.


.. rubric:: Footnotes

.. [#example-dir] The source code of this example and all other in
   this chapter are included in the Leon distribution.  Examples about
   lists can be found in ``library/collection/List.scala``, the other
   examples are located in the ``testcases/verification/proof/``
   directory.

.. [#props-not-types] Perhaps surprisingly, propositions and proofs
   live in the same universe in Leon.  This is contrary to
   e.g. type-theoretic proof assistants where propositions are
   represented by types and proofs are terms inhabiting such types.

.. [#dicrete-meas] To be precise, we are assuming here the underlying
   measurable space :math:`(A, \mathcal{P}(A))`, where :math:`A` is
   countable and :math:`\mathcal{P}(A)` denotes its discrete σ-algebra
   (i.e. the power set of :math:`A`).
