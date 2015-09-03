.. _synthesis:

Synthesis
=========

Software synthesis offers an alternative way of developing trustworthy
programs. At a high level, program specifications describe **what** the
function should do, and its corresponding implementation describes **how** it
will do it. While verification ensures that both views match, synthesis
consists of translating these specifications (or expectations) to executable
programs which realises them.

As we have seen previously, relatively precise specifications of complex
operations can be written concisely. Synthesis can thus reduce development time
and allows the user to focus on high-level aspects.

Deductive Synthesis Framework
-----------------------------

The synthesizer takes a synthesis problem that it extracts from ``choose`` or
holes (``???``) found in the program. Formally, we define a **synthesis problem** as

.. math::

    [[ ~~ \bar{a} ~~ \langle ~~ \Pi \rhd \phi ~~ \rangle ~~  \bar{x} ~~ ]]


which carries the following information:

 * a set of input variables :math:`\bar{a}`, initially all variables in scope of the ``choose``,
 * a set of output variables :math:`\bar{x}`, corresponding to the values to synthesize,
 * a path-condition :math:`\Pi`, constraining :math:`\bar{a}`,
 * the specification :math:`\phi` relating input variables to output variables.

The job of the synthesizer is to convert this problem into a solution :math:`[ ~ P ~ | ~ T ~ ]`, which consists of

 * a executable program term :math:`T` (an expression that may contain input variables),
 * a precondition  :math:`P` under which this program is valid

To illustrate, we consider the following program:

.. code-block:: scala

  def foo(a: BigInt, b: BigInt): Int = {
    if (a > b) {
      choose ( (x: BigInt) => x > a)
    } else {
      0
    }
  }


From this program, we will extract the following initial synthesis problem:

.. math::

    [[ ~~ a, b ~~ \langle ~~ a > b ~ \rhd ~ x > a ~~ \rangle ~~  x ~~ ]]

A possible solution to this problem would be:

.. math::

   [ ~ \top ~ | ~ a + 1 ~ ]

To solve this problem, the synthesizer will apply a series of rules which will
try to either

 1. Decompose this problem into sub problems, which may be simpler to solve
 2. Immediately find a solution


This corresponds to an and-or graph of rule applications, which Leon will
explore.


Decomposing Rules
-----------------

Leon defines several rules that decompose a synthesis problem (a ``choose``)
into sub-problems that may be simpler to solve. Such rules also define a way to
generate a solution for the original problem, when provided with solutions for
all of the sub-problems. These rules thus both decompose the problems and
recompose the solutions. Leon defines several of such decomposing rules:

Equality Split
^^^^^^^^^^^^^^

Given two input variables `a` and `b` of compatible types, this rule
considers the cases where `a = b` and `a != b`. From:

.. code-block:: scala

  choose(res => spec(a, b, res))


this rule generates two sub-chooses, and combines them as follows:

.. code-block:: scala

   if (a == b) {
     choose(res => spec(a, a, res))
   } else {
     choose(res => spec(a, b, res))
   }


Inequalite Split
^^^^^^^^^^^^^^^^

Given two input variables `a` and `b` of numeric type, this rule
considers the cases where `a < b`, `a == b`, and `a > b`. From:

.. code-block:: scala

  choose(res => spec(a, b, res))


this rule generates three sub-chooses, and combines them as follows:

.. code-block:: scala

   if (a < b) {
     choose(res => spec(a, b, res))
   } else if (a > b) {
     choose(res => spec(a, b, res))
   } else {
     choose(res => spec(a, a, res))
   }


ADT Split
^^^^^^^^^

Given a variable `a` typed as an algebraic data type `T`, the rules decomposes
the problem in cases where each case correspond to one subtype of `T`:

.. code-block:: scala

  abstract class T
  case class A(f1: Int) extends T
  case class B(f2: Boolean) extends T
  case object C extends T

  choose(res => spec(a, res))


this rule generates three sub-chooses, in which the input variable `a` is
substituted by the appropriate case, and combines them as follows:

.. code-block:: scala

   a match {
     case A(f1) => choose(res => spec(A(f1), res))
     case B(f2) => choose(res => spec(B(f2), res))
     case C     => choose(res => spec(C, res))
   }


Int Induction
^^^^^^^^^^^^^

Given an Int (or BigInt) variable `a`, the rules performs induction on `a`:

.. code-block:: scala

  choose(res => spec(a, res))


this rule generates three sub-chooses, one for the base case and one for each inductive case (we allow negative numbers):

.. code-block:: scala

   def tmp1(a: Int) = {
     if (a == 0) {
       choose(res => spec(a, res))
     } else if (a > 0) {
       val r1 = tmp1(a-1)
       choose(res => spec(a, res))
     } else if (a < 0) {
       val r1 = tmp1(a+1)
       choose(res => spec(a, res))
     }
   }

   tmp1(a)

This allows Leon to synthesize a well-structured recursive function.

One Point
^^^^^^^^^

This syntactic rule considers equalities of an output variable at the top level of the
specification, and substitutes the variable with the corresponding expression in
the rest of the formula. Given the following specification:

.. math::
    res1 = expr \land \phi
  
and assuming :math:`expr` does not use :math:`a`, we generate the alternative and
arguable simpler specification:


.. math::
    \phi[res1 \rightarrow expr]


Assert
^^^^^^

The `Assert` rule scans the specification for predicates that only constraint
input variables and lifts them out of the specification. Since these are
constraints over the input variables, they typically represent the
precondition necessary for the ``choose`` to be feasible.
Given an input variable `a`:

.. code-block:: scala

  choose(res => spec(a, res) && pred(a))

will become:

.. code-block:: scala

  require(pred(a))

  choose(res => spec(a, res))

Case Split
^^^^^^^^^^

This rule considers a top-level disjunction and decomposes it:

.. code-block:: scala

  choose(res => spec1(a, res) || spec2(a, res))

thus becomes two sub-chooses

.. code-block:: scala

  if (P) {
    choose(res => spec1(a, res))
  } else {
    choose(res => spec2(a, res))
  }

Here we note that ``P`` is not known until the first ``choose`` is solved, as it
corresponds to its precondition.



Equivalent Input
^^^^^^^^^^^^^^^^

This rule discovers equivalences in the input variables in order to eliminate
redundancies. We consider two kinds of equivalences:

 1) Simple equivalences: the specification contains  :math:`a = b` at the top
 level.

 2) ADT equivalence the specification contains :math:`l.isInstanceOf[Cons]
 \land h = l.head \land t = l.tail` which entails :math:`l = Cons(h, t)` and
 thus allows us to substitute :math:`l` by :math:`Cons(h, t)`.

Eliminating equivalences prevents explosion of redundant rule instantiations.
For instance, if you have four integer variables where three of them are
equivalent, Leon has 6 ways of applying `Inequality Split`. After
eliminating equivalences, only one application remains possible.

Unused Input
^^^^^^^^^^^^

This rule tracks input variables (variables originally in scope of the
``choose``) that are not constrained by the specification or the
path-condition. These input variables carry no information and are thus
basically useless. The rule consequently eliminates them from the set of input
variables with which rules may be instantiated.

Unconstrained Output
^^^^^^^^^^^^^^^^^^^^

This rule is the dual of ``Unused Input``: it tracks output variable (result
values) that are not constrained. Such variables can be trivially synthesized
by any value or expression of the right type. For instance: 

.. code-block:: scala

  choose ((x: Int, y: T) => spec(y))

becomes

.. code-block:: scala

  (0, choose ((y: T) => spec(y)))

Leon will use the simplest value of the given type, when available. Note this
rule is not able to synthesize variables of generic types, as no literal values
exist for these. While ``null`` may be appropriate in Scala, Leon does not
define it.

..
    Unification.DecompTrivialClash,
    Disunification.Decomp,
    ADTDual,
    CaseSplit,
    IfSplit,
    DetupleOutput,
    DetupleInput,
    InnerCaseSplit

Closing Rules
-------------

While decomposing rules split problems in sub-problems, Leon also defines rules
that are able to directly solve certain synthesis problems. These rules are
crucial for the synthesis search to terminate efficiently. We define several
closing rules that apply in different scenarios:

Ground
^^^^^^

This rule applies when the synthesis problem has no input variables. If the
specification is satisfiable, its model corresponds to a valid solution. We
rely on SMT solvers to check satisfiability of the formulas. For instance:

.. code-block:: scala

  choose ((x: Int, y: Int) => x > 42 && y > x)

can trivially be synthesized by ``(1000, 1001)``.

If the specification turns out to be UNSAT, the synthesis problem is impossible
and we synthesize it as an ``error`` with a ``false`` precondition.


Optimistic Ground
^^^^^^^^^^^^^^^^^

This rule acts like `Ground`, but without the requirement on the absence of input
variables. The reasoning is that even though the problem has input variables,
the solutions might still be a constant expression.

`Optimistic Ground` also tries to satisfy the specification, but it also needs
to validate the resulting model. That is, given a valuation of output
variables, it checks whether it exists a valuation for input variables such that
the specification is violated. The model is discarded if such counter-example
is found. If no counter-example exist, we solve the synthesis problem with the
corresponding values.

The rule tries at most three times to discover a valid value.

CEGIS
^^^^^

`CEGIS` stands for Counter-Example-Guided Inductive Synthesis, it explores the
space of small expressions to find valid solutions. Here we represent the space
of programs by a tree, where branches are determined by free boolean variables.
For instance, a tree for small integer operations could be:

.. code-block:: scala

  def res(b, a1, a2) =      if (b1) 0
                       else if (b2) 1
                       else if (b3) a1
                       else if (b4) a2
                       else if (b5) c1(b, a1, a2) + c2(b, a1, a2)
                       else         c1(b, a1, a2) * c2(b, a1, a2)

  def c1(b, a1, a2)  =      if (b7) 0
                       else if (b8) 1
                       else if (b9) a1
                       else         a2

  def c2(b, a1, a2)  =      if (b10) 0
                       else if (b11) 1
                       else if (b12) a1
                       else          a2

At a high-level, it consists of the following loop:

 1. Find one expression and inputs that satisfies the specification:
    :math:`\exists \bar{b}, a1, a2. spec(a1, a2, res(\bar{b}, a1, a2))`.
    If this fails, we know that the solution is not in the search space.
    If this succeeds, we:

 2. Validate the expression represented by :math:`M_\bar{b}` for all inputs by
    searching for a counter-example: :math:`\exists a1, a2. \lnot spec(a1, a2, res(M_\bar{b}, a1, a2))`. 
    If such counter-example exists, start over with (1) with this program
    excluded. If no counter-example exists we found a valid expression.

The space of expressions our CEGIS rule considers is small expressions of
bounded depth (3), which contain for each type: a few literals, functions and
operations returning that type that do not transitively call the function under
synthesis (to prevent infinite loops), and recursive calls where one argument is
decreasing.


TEGIS
^^^^^

This rule uses the same search space as `CEGIS` but relies only on tests
(specified by the user or generated) to validate expressions. It is thus a
generally faster way of discovering candidate expressions. However, these
expressions are not guaranteed to be valid since they have only been validated
by tests. Leon's synthesis framework supports untrusted solutions which trigger
an end-to-end validation step that relies on verification.
