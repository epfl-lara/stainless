.. _tutorial:

Tutorial: Sorting
=================

This tutorial shows how to:

  * use `ensuring`, `require`, and `holds` constructs
  * learn the difference between `Int` and `BigInt`
  * define lists as algebraic data types
  * use sets and recursive function to specify data structures

See :doc:`gettingstarted` about how to setup the command line
tool.

Warm-up: Max
------------

As a warm-up illustrating verification, we define and debug a `max` function
and specify its properties. Stainless uses Scala constructs
`require` and `ensuring` to document preconditions and
postconditions of functions. Note that, in addition to
checking these conditions at run-time (which standard Scala
does), Stainless can analyze the specifications statically and
prove them for *all* executions, or, if they are wrong, automatically find
inputs for which the conditions fail.

Consider the following definition inside of an object `TestMax`.

.. code-block:: scala

  object TestMax {
    def max(x: Int, y: Int): Int = {
      val d = x - y
      if (d > 0) x
      else y
    } ensuring(res =>
      x <= res && y <= res && (res == x || res == y))
  }

A Stainless program consists of one or more modules delimited by
`object` and `class` declarations.
The code of `max` attempts to compute the maximum of two given arguments
by subtracting them. If the result is positive, it returns
the first one, otherwise, it returns the second one.

To specify the correctness of the computed result, we use
the `ensuring` clause.  In this case, the clause specifies
that the result is larger than `x` and than `y`, and that it
equals to one of them. The construct `ensuring(res => P)`
denotes that, if we denote by `res` the return value of the
function, then `res` satisfies the boolean-valued expression
`P`.  The name `res` we chose is an arbitrary bound variable
(even though we often tend to use `res`).

We can evaluate this code on some values by writing
parameterless functions and inspecting what they evaluate
to. The web interface will display these results for us.

.. code-block:: scala

  def test1 = max(10, 5)
  def test2 = max(-5, 5)
  def test3 = max(-5, -7)

The code seems to work correctly on the example values.
However, Stainless automatically finds that it is not correct:

.. code-block:: text

   [  Info  ]  - Now solving 'postcondition' VC for max @6:16...
   [  Info  ]  - Result for 'postcondition' VC for max @6:16:
   [Warning ]  => INVALID
   [Warning ] Found counter-example:
   [Warning ]   y: Int -> 2147483647
   [Warning ]   x: Int -> -2147483648

   [  Info  ]  - Now solving 'postcondition' VC for max @7:10...
   [  Info  ]  - Result for 'postcondition' VC for max @7:10:
   [Warning ]  => INVALID
   [Warning ] Found counter-example:
   [Warning ]   y: Int -> -2147483648
   [Warning ]   x: Int -> 1

   [  Info  ]  - Now solving 'body assertion: Subtraction overflow' VC for max @5:13...
   [  Info  ]  - Result for 'body assertion: Subtraction overflow' VC for max @5:13:
   [Warning ]  => INVALID
   [Warning ] Found counter-example:
   [Warning ]   y: Int -> -2147483648
   [Warning ]   x: Int -> 0

Here, Stainless emits three distinct verification conditions:

* One which corresponds to the postcondition of ``max`` when we take the `then` branch
  of the ``if`` statement, on line 6.

* Another one for the postcondition of ``max`` when we take the `else` branch
  of the ``if`` statement, on line 7.

* A last one with an overflow check for the subtraction on line 5.

Let us look at the first verification condition:

.. code-block:: text

    - Now solving 'postcondition' VC for max @6:16...
    - Result for 'postcondition' VC for max @6:16:
    => INVALID
   Found counter-example:
     y: Int -> 2147483647
     x: Int -> -2147483648

Stainless tells us that it found two input for which the ``ensuring`` clause of the
``max`` function evaluates to ``false``. The second verification is similar.

We may wish to define a test method

.. code-block:: scala

  def test4 = max(-1639624704, 1879048192)

whose evaluation indeed results in ``ensuring`` condition being violated.
The problem is due to overflow of 32-bit integers, due to which
the value `d` becomes positive, even though `x` is negative and thus smaller than
the large positive value `y`.

In fact, Stainless alerts us of this very problem in the third verification condition,
to help us pin point the place where the overflow occured.

.. note::

   As in Scala, the `Int` type denotes 32-bit integers with the usual signed arithmetic
   operations from computer architecture and the JVM specification.

To use unbounded integers, we simply change the types to
`BigInt`, obtaining a program that verifies (and, as
expected, passes all the test cases).

.. code-block:: scala

    def max(x: BigInt, y: BigInt): BigInt = {
      val d = x - y
      if (d > 0) x
      else y
    } ensuring(res =>
      x <= res && y <= res && (res == x || res == y))

As a possibly simpler specification, we could have also
defined the reference implementation

.. code-block:: scala

  def rmax(x: BigInt, y: BigInt) = {
    if (x <= y) y else x
  }

and then used as the postcondition of `max` simply

.. code-block:: scala

  ensuring (res =>  res == rmax(x,y))

In general, Stainless uses both function body and function
specification when reasoning about the function and its
uses. Thus, we need not repeat in the postcondition those
aspects of function body that follow directly through
inlining the function, but we may wish to state those
that require induction to prove.

The fact that we can use functions in preconditions
and postconditions allows us to state fairly general
properties. For example, the following lemma verifies
a number of algebraic properties of `max`.

.. code-block:: scala

  def max_lemma(x: BigInt, y: BigInt, z: BigInt): Boolean = {
    max(x,x) == x &&
    max(x,y) == max(y,x) &&
    max(x,max(y,z)) == max(max(x,y), z) &&
    max(x,y) + z == max(x + z, y + z)
  } holds

Here `holds` operator on the function body is an
abbreviation for the postcondition stating that the returned
result is always true, that is, for

.. code-block:: scala

  ensuring(res => res==true)

As a guideline, we typically use `holds` to express such
algebraic properties that relate multiple invocations of
functions, whereas we use `ensuring` to document property of
an arbitrary single invocation of a function. Stainless is more likely to automatically
use the property of a function if it is associated with it using
`ensuring` than using an external lemma.

Going back to our buggy implementation of `max` on `Int`-s,
an alternative to using `BigInt`-s is to decide that
the method should only be used under certain conditions,
such as `x` and `y` being non-negative. To specify the
conditions on input, we use the `require` clause.

.. code-block:: scala

  def max(x: Int, y: Int): Int = {
    require(0 <= x && 0 <= y)
    val d = x - y
    if (d > 0) x
    else y
  } ensuring (res =>
    x <= res && y <= res && (res == x || res == y))

This program verifies and indeed works correctly on
non-negative 32-bit integers as inputs.

**Question:** What if we restrict the inputs to `max` to be
`a)` non-positive, or `b)` strictly negative? Modify the
`require` clause for each case accordingly and explain the
behavior of Stainless. See the note below, as well.

.. note::

   By default, Stainless will emit verification conditions to
   check that arithmetic operations on sized integers such as
   `Int` cannot overflow. To opt-out of this behavior, eg. when
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

We use a recursive algebraic data type
definition, expressed using Scala's **case classes**.

.. code-block:: scala

  sealed abstract class List
  case object Nil extends List
  case class Cons(head: BigInt, tail: List) extends List

We can read the definition as follows: the set of lists is
defined as the least set that satisfies them:

  * empty list `Nil` is a list
  * if `head` is an integer and `tail` is a `List`, then
    `Cons(head,tail)` is a `List`.

Each list is constructed by applying the above two rules
finitely many times.  A concrete list containing elements 5,
2, and 7, in that order, is denoted

.. code-block:: scala

    Cons(5, Cons(2, Cons(7, Nil)))

Having defined the structure of lists, we can move on to
define some semantic properties of lists that are of
interests. For this purpose, we use recursive functions
defined on lists.

Size of a List
^^^^^^^^^^^^^^

As the starting point, we define the size of a list.

.. code-block:: scala

    def size(l: List) : BigInt = (l match {
        case Nil => 0
        case Cons(x, rest) => 1 + size(rest)
    })

The definition uses *pattern matching* to define size of the
list in the case it is empty (where it is zero) and when it
is non-empty, or, if it's non-empty, then it has a head `x`
and the rest of the list `rest`, so the size is one plus the
size of the rest. Thus `size` is a recursive function.  A
strength of Stainless is that it allows using such recursive
functions in specifications.

It makes little sense to try to write a complete
specification of `size`, given that its recursive definition
is already a pretty clear description of its
meaning. However, it is useful to add a consequence of this
definition, namely that the size is non-negative. The reason
is that Stainless most of the time reasons by unfolding `size`,
and the property of size being non-negative is not revealed
by such unfolding. Once specified, the non-negativity is
easily proven and Stainless will make use of it.

.. code-block:: scala


    def isize(l: List) : Int = (l match {
      case Nil => 0
      case Cons(x, rest) => {
        val rSize = isize(rest)
        if (rSize == Int.MaxValue) rSize
        else 1 + rSize
      }
    }).ensuring(res => res >= 0)

In some cases, it may be helpful to define a size function
that returns a bounded integer type, such as the 32-bit signed integer ```Int``.
One useful way to do this is to define function as follows:

.. code-block:: scala

    def isize(l: List) : Int = (l match {
        case Nil => 0
        case Cons(x, rest) => {
          val rSize = isize(rest)
          if (rSize == Int.Max) rSize
          else 1 + rSize
        }
    }) ensuring(res => res >= 0)

The above ``isize`` function satisfies the usual recursive definition for all but a huge
lists, returns a non-negative integer, and ensures that if isize returns a small
number, then the list is indeed small.

Sorted Lists
^^^^^^^^^^^^

We define properties of values simply as executable
predicates that check if the property holds. The following
is a property that a list is sorted in a strictly ascending
order.

.. code-block:: scala

    def isSorted(l : List) : Boolean = l match {
      case Nil => true
      case Cons(_,Nil) => true
      case Cons(x1, Cons(x2, rest)) =>
        x1 < x2 && isSorted(Cons(x2,rest))
    }

Insertion into Sorted List
--------------------------

Consider the following specification of insertion into a sorted list. It's a
building block for an insertion sort.

.. code-block:: scala

  def sInsert(x : BigInt, l : List) : List = {
    require(isSorted(l))
    l match {
      case Nil => Cons(x, Nil)
      case Cons(e, rest) if (x == e) => l
      case Cons(e, rest) if (x < e) => Cons(x, Cons(e,rest))
      case Cons(e, rest) if (x > e) => Cons(e, sInsert(x,rest))
    }
  } ensuring {(res:List) => isSorted(res)}

Stainless verifies that the returned list is indeed sorted. Note
how we are again using a recursively defined function to
specify another function. We can introduce a bug into the
definition above and examine the counterexamples that Stainless
finds.

Being Sorted is Not Enough
--------------------------

Note, however, that a function such as this one is also correct.

.. code-block:: scala

    def fsInsert(x : BigInt, l : List) : List = {
      require(isSorted(l))
      Nil
    } ensuring {(res:List) => isSorted(res)}

So, our specification may be considered weak, because it does
not say anything about the elements.

Using Size in Specification
---------------------------

Consider a stronger additional postcondition property:

.. code-block:: scala

  size(res) == size(l) + 1

Does it hold? If we try to add it, we obtain a counterexample.
A correct strengthening, taking into account that the element
may or may not already be in the list, is the following.

.. code-block:: scala

  size(l) <= size(res) && size(res) <= size(l) + 1

Using Content in Specification
------------------------------

A stronger specification needs to talk about the `content`
of the list.

.. code-block:: scala

  def sInsert(x : BigInt, l : List) : List = {
    require(isSorted(l))
    l match {
      case Nil => Cons(x, Nil)
      case Cons(e, rest) if (x == e) => l
      case Cons(e, rest) if (x < e) => Cons(x, Cons(e,rest))
      case Cons(e, rest) if (x > e) => Cons(e, sInsert(x,rest))
    }
  } ensuring {(res:List) =>
     isSorted(res) && content(res) == content(l) ++ Set(x)}

To compute `content`, in this example we use sets (even
though in general, it might be better to use bags
i.e. multisets).

.. code-block:: scala

  def content(l: List): Set[BigInt] = l match {
    case Nil => Set()
    case Cons(i, t) => Set(i) ++ content(t)
  }


This completes the tutorial. To learn more, check the rest of this
documentation and browse the examples provided with Stainless.
