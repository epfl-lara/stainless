.. _tutorial:

Tutorial: Sorting
=================

This tutorial shows how to:

  * use ``ensuring``, ``require``, and ``holds`` constructs
  * learn the difference between ``Int`` and ``BigInt``
  * define lists as algebraic data types
  * use sets and recursive functions to specify data structures

See :doc:`gettingstarted` about how to set up the command line tool.

Warm-up: Max
------------

As a warm-up illustrating verification, we define and debug a ``max`` function
and specify its properties. Stainless uses Scala constructs ``require`` and
``ensuring`` to document pre-conditions and post-conditions of functions. 

Note that in addition to checking these conditions at run-time (which standard
Scala does), Stainless can analyze the specifications *statically* and prove
them for *all* executions. Or, if they are wrong, automatically find inputs for
which the conditions fail.

Consider the following function definition. Paste it into a file called
``test.scala``.

.. code-block:: scala
  :linenos:

  def max(x: Int, y: Int): Int = {
    val d = x - y
    if d > 0 then x
    else y
  }.ensuring(res =>
    x <= res && y <= res && (res == x || res == y)
  )

A Stainless program consists of one or more modules delimited by ``object`` and
``class`` declarations. The function ``max`` attempts to compute the maximum of
two given arguments by subtracting them. If the result is positive, it returns
the first one, otherwise, it returns the second one.

To specify the correctness of the computed result, we use the ``ensuring``
clause at the end of the function body. In this case, the clause specifies that
the result is larger than both ``x`` and ``y``, and that it equals (at least)
one of them. The construct ``ensuring(res => P)`` denotes that, if we denote by
``res`` the return value of the function, then ``res`` satisfies the
boolean-valued expression ``P``.  The name ``res`` we chose is an arbitrary
bound variable (even though we often tend to use ``res``, for *result*).

The ``ensuring`` clause is called the *post-condition* of the function.

We can evaluate this code on some values by writing parameter-less functions and
asking Stainless to additionally evaluate them.

.. code-block:: scala

  def test1 = max(10, 5)
  def test2 = max(-5, 5)
  def test3 = max(-5, -7)

To evaluate them, we run Stainless as:

.. code-block:: bash

  $ stainless test.scala --eval

The code seems to work correctly on the example values. However, Stainless
automatically finds that it is not correct:

.. stainless output; the postconditions are the highlighted lines!!
.. code-block:: text
  :emphasize-lines: 1,10,19
  :linenos:

  [Warning ]  - Result for 'body assertion: Subtraction overflow' VC for max @3:13:
  [Warning ] (x & -2147483648) == (y & -2147483648) || (x & -2147483648) == (x - y & -2147483648)
  [Warning ] testMax.scala:3:13:  => INVALID
                val d = x - y
                        ^^^^^
  [Warning ] Found counter-example:
  [Warning ]   x: Int -> 0
  [Warning ]   y: Int -> -2147483648
  [  Info  ]  Verified: 0 / 3
  [Warning ]  - Result for 'postcondition' VC for max @7:37:
  [Warning ] !(x - y > 0) || x <= x && y <= x
  [Warning ] testMax.scala:7:37:  => INVALID
                x <= res && y <= res && (res == x || res == y)
                                                ^
  [Warning ] Found counter-example:
  [Warning ]   x: Int -> -1361256659
  [Warning ]   y: Int -> 1543503872
  [  Info  ]  Verified: 0 / 3
  [Warning ]  - Result for 'postcondition' VC for max @7:49:
  [Warning ] x - y > 0 || x <= y && y <= y
  [Warning ] testMax.scala:7:49:  => INVALID
                x <= res && y <= res && (res == x || res == y)
                                                            ^
  [Warning ] Found counter-example:
  [Warning ]   x: Int -> 1879048191
  [Warning ]   y: Int -> -2147483646

Here, Stainless emits three distinct verification conditions:

* One with an overflow check for the subtraction on line 1 of the report,

* another one for the post-condition of ``max`` when we take the ``else`` branch
  of the ``if`` statement, on line 10 of the report, and

* a final one which corresponds to the post-condition of ``max`` when we take
  the ``then`` branch of the ``if`` statement, on line 19 of the report.


Let us look at the post-condition violations:

.. code-block:: text

  [Warning ]  - Result for 'postcondition' VC for max @7:49:
  [Warning ] x - y > 0 || x <= y && y <= y
  [Warning ] testMax.scala:7:49:  => INVALID
                x <= res && y <= res && (res == x || res == y)
                                                            ^
  [Warning ] Found counter-example:
  [Warning ]   x: Int -> 1879048191
  [Warning ]   y: Int -> -2147483646

Stainless tells us that it found an input pair for which the ``ensuring`` clause
of the ``max`` function evaluates to ``false``. The other branch is similar.

We can attempt to evaluate this with Stainless as before: 

.. code-block:: scala

  def testCounter = max(1879048191, -2147483646) 
  // => CRASHED
  // Postcondition @5:32

and the evaluation indeed results in the ``ensuring`` condition being violated.
The problem is due to overflow of 32-bit integers, due to which the value ``d``
becomes negative, even though ``x`` is positive and thus larger than the
negative value ``y``.

In fact, Stainless alerts us of this very problem in the final verification
condition we can look at, to help us pinpoint the place where the overflow
occurred.

.. note::

   As in standard Scala, here, the ``Int`` type denotes 32-bit integers with the
   usual signed arithmetic operations from computer's architecture and the JVM
   specification.

To use *unbounded* integers, we simply change the types to
``BigInt``, obtaining a program that verifies (and, as
expected, passes all the test cases).

.. code-block:: scala

  def max(x: BigInt, y: BigInt): BigInt = {
    val d = x - y
    if d > 0 then x
    else y
  }.ensuring(res =>
    x <= res && y <= res && (res == x || res == y)
  )

Note that the "subtraction overflow" verification condition vanishes altogether!
Arithmetic operations over ``BigInt``, i.e., mathematical integers, cannot
overflow.

As a possibly simpler specification, we could have also
defined the reference implementation

.. code-block:: scala

  def rmax(x: BigInt, y: BigInt) = {
    if x <= y then y else x
  }

and then used as the post-condition of ``max`` simply

.. code-block:: scala

  ensuring (res =>  res == rmax(x,y))

In general, Stainless uses both a function's body and its specification when
reasoning about the function and its applications. Thus, we need not repeat
aspects of function body that follow directly through inlining the function in
the post-condition, but we may wish to state more complex properties that
require *induction* to prove.

The fact that we can use functions in preconditions and post-conditions allows
us to state fairly general properties. For example, the following lemma verifies
a number of algebraic properties of ``max``.

.. code-block:: scala

  def max_lemma(x: BigInt, y: BigInt, z: BigInt): Unit = {
    ()
  }.ensuring { _ =>
    max(x,x) == x &&
    max(x,y) == max(y,x) &&
    max(x,max(y,z)) == max(max(x,y), z) &&
    max(x,y) + z == max(x + z, y + z)
  }

Here, the function does not compute *anything*. It simply states that some
properties must hold, independent of this function's result (note the underscore
in the ``ensuring`` clause argument).

As a guideline, we typically use such a lemma to express algebraic properties
that relate multiple invocations of functions, whereas we add directly to the
function definition properties of an arbitrary single invocation of a function,
which define its behavior.

Stainless is more likely to automatically use properties of a function in
further reasoning if they are associated with the ``ensuring`` clause in its
body rather than in an external lemma.

Going back to our buggy implementation of ``max`` on ``Int``-s, an alternative
to using ``BigInt``-s is to decide that the method should only be used under
certain conditions, such as ``x`` and ``y`` being non-negative. To specify the
conditions on input, we use the ``require`` clause.

Properties appearing in a ``require`` clause are called the
*pre-condition* of the function.

The pre-condition and post-condition of a function together form its
*specification*.

.. code-block:: scala

  def max(x: Int, y: Int): Int = {
    require(0 <= x && 0 <= y)
    val d = x - y
    if d > 0 then x
    else y
  }.ensuring(res =>
    x <= res && y <= res && (res == x || res == y)
  )

This program verifies and indeed works correctly on
non-negative 32-bit integers as inputs.

.. admonition:: Question
  :class: tip

  What if we restrict the inputs to ``max`` to be
  
  a. non-positive, or 
  b. strictly negative? 
  
  Modify the ``require`` clause for each case accordingly and predict the
  behavior of Stainless' verification. Does it match the returned report?
  
  See the note below, as well.

.. note::

   By default, Stainless will emit verification conditions to
   check that arithmetic operations on sized integers such as
   `Int` cannot overflow. To opt-out of this behavior, e.g. when
   such wrapping semantics are desired, one can wrap the offending
   expression in a call to `stainless.math.wrapping`:

   .. code-block:: scala

      import stainless.math.wrapping

      def doubleOverflow(x: Int): Int = {
         wrapping { x + x }
      }

In the sequel, we will mostly use `BigInt` types.

Defining Lists and Their Properties
-----------------------------------

We next consider sorting an unbounded number of elements.
For this purpose, we define a data structure for lists of
integers.  Stainless has a built-in data type of parametric
lists, see :doc:`library`, but here we define
our own variant instead.

Lists
^^^^^

We use a recursive algebraic data type definition, expressed using Scala's
**case classes**.

.. code-block:: scala

  sealed trait List
  case object Nil extends List
  case class Cons(head: BigInt, tail: List) extends List

We can read the definition as follows: the set of lists is
defined as the least set that satisfies them:

  * empty list ``Nil`` is a list
  * if ``head`` is an integer and ``tail`` is a ``List``, then
    ``Cons(head,tail)`` is a ``List``.

Each list is constructed by applying the above two rules
finitely many times.  A concrete list containing elements 5,
2, and 7, in that order, is denoted

.. code-block:: scala

    Cons(5, Cons(2, Cons(7, Nil)))

Having defined the structure of lists, we can move on to define some semantic
properties of lists that are of interest. For this purpose, we use recursive
functions defined on lists.

Size of a List
^^^^^^^^^^^^^^

As the starting point, we define the size of a list.

.. code-block:: scala

    def size(l: List) : BigInt = {
      l match
          case Nil => 0
          case Cons(x, rest) => 1 + size(rest)
    }

The definition uses *pattern matching* to define size of the list in the case it
is empty (where it is zero) and when it is non-empty, or, if it's non-empty,
then it has a head ``x`` and the rest of the list ``rest``, so the size is one
plus the size of the rest. Thus, ``size`` is a recursive function.  A strength
of Stainless is that it allows using such recursive functions in specifications.

It makes little sense to try to write a complete specification of ``size``,
given that its recursive definition is already a pretty clear description of its
meaning. However, it is useful to add a consequence of this definition, namely
that the size is non-negative. The reason is that Stainless most of the time
reasons by unfolding ``size``, and the property of size being non-negative is
not revealed by such unfolding sequences. Once specified, the non-negativity is
easily proven and Stainless will make use of it.

.. code-block:: scala

    def size(l: List) : BigInt = {
      l match
          case Nil => 0
          case Cons(x, rest) => 1 + size(rest)
    }.ensuring(res => res >= 0)

In some cases, it may be helpful to define a size function that returns a
bounded integer type, such as the 32-bit signed integer type ``Int``. One useful
way to do this is to define a function as follows:

.. code-block:: scala

    def isize(l: List) : Int = {
      l match
        case Nil => 0
        case Cons(x, rest) =>
          val rSize = isize(rest)
          if rSize == Int.MaxValue then rSize
          else 1 + rSize
    }.ensuring(res => res >= 0)

The ``isize`` function above satisfies the usual recursive definition for all
but huge lists, returns a non-negative integer, and further ensures that if
``isize`` returns a small number, then the list is indeed small.

Sorted Lists
^^^^^^^^^^^^

We can define properties of values simply as executable predicates that check if
the property holds. 

The following is a property that a list is sorted in a strictly ascending order.

.. code-block:: scala

    def isSorted(l : List) : Boolean = 
      l match
        case Nil => true
        case Cons(_,Nil) => true
        case Cons(x1, Cons(x2, rest)) =>
          x1 < x2 && isSorted(Cons(x2,rest))

Insertion into Sorted List
--------------------------

Now that we have defined what it means for a list to be sorted, we can write
functions *on sorted lists* and check their properties. Consider the following
specification of insertion into a sorted list. It's a building block for an
insertion sort.

.. code-block:: scala

  def sInsert(x : BigInt, l : List) : List = {
    require(isSorted(l))
    l match
      case Nil => Cons(x, Nil)
      case Cons(e, rest) if (x == e) => l
      case Cons(e, rest) if (x < e) => Cons(x, Cons(e,rest))
      case Cons(e, rest) if (x > e) => Cons(e, sInsert(x,rest))
  }.ensuring { res => isSorted(res) }

Stainless verifies that the returned list is indeed sorted. Note how we are once
again using a recursively defined function to specify another function. 

.. admonition:: Experiment
  :class: important

  Introduce a bug in the definition of ``sInsert`` to make it violate its
  post-condition. What kind of counterexamples do you get from Stainless?

Being Sorted is Not Enough
--------------------------

Note, however, that a function such as this one is also correct.

.. code-block:: scala

    def fsInsert(x : BigInt, l : List) : List = {
      require(isSorted(l))
      Nil
   }.ensuring { res => isSorted(res) }

So, while our specification is *valid*, it is too *weak* to specify insertion,
because it does not say anything about the elements.

Using Size in Specification
---------------------------

Consider a stronger additional post-condition property:

.. code-block:: scala

  size(res) == size(l) + 1

Does it hold? If we try to add it to ``sInsert``, we obtain a counterexample. A
correct strengthening, taking into account that the element may or may not
already be in the list, is the following.

.. code-block:: scala

  size(l) <= size(res) && size(res) <= size(l) + 1

Using Content in Specification
------------------------------

A stronger specification needs to talk about the ``content`` of the list.

.. code-block:: scala

  def sInsert(x : BigInt, l : List) : List = {
    require(isSorted(l))
    l match
      case Nil => Cons(x, Nil)
      case Cons(e, rest) if (x == e) => l
      case Cons(e, rest) if (x < e) => Cons(x, Cons(e,rest))
      case Cons(e, rest) if (x > e) => Cons(e, sInsert(x,rest))
  }.ensuring { res =>
     isSorted(res) && content(res) == content(l) ++ Set(x)
  }

Of course, we need to define what the "content" of a list is. In this example,
we use sets (even though in general, it might be better to use bags i.e.
multisets).

.. code-block:: scala

  import stainless.lang.*

  def content(l: List): Set[BigInt] = 
    l match 
      case Nil => Set.empty
      case Cons(i, t) => content(t) ++ Set(i)


This completes the tutorial. To learn more, check the rest of this documentation
and browse the examples provided with Stainless, as well as the `epfl-lara/bolts
library <https://github.com/epfl-lara/bolts>`.
