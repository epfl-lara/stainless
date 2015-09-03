.. _tutorial:

Tutorial: Sorting
=================

This tutorial shows how to:

  * use `ensuring`, `require`, and `holds` constructs
  * learn the difference between `Int` and `BigInt`
  * use the `choose` construct for synthesis and constraint solving
  * define lists as algebraic data types
  * use sets and recursive function to specify data structures
  * synthesize insertion into a sorted list
  * synthesize sorting on lists
  * repair an incorrect function

We assume that the user is using the web interface. The
functionality is also available (possibly with less
convenient interface) from the command line, see
:ref:`gettingstarted`.

Warm-up: Max
------------

As a warm-up illustrating verification, we define and debug a `max` function 
and specify its properties.  Leon uses Scala constructs
`require` and `ensuring` to document preconditions and
postconditions of functions. Note that, in addition to
checking these conditions at run-time (which standard Scala
does), Leon can analyze the specifications statically and
prove them for *all* executions, or, if they are wrong, automatically find
inputs for which the conditions fail. (Moreover, it can
execute specifications alone without the code, 
it can do synthesis, and repair.)

Consider the following definition inside an object `TestMax`.

.. code-block:: scala

  object TestMax {
    def max(x: Int, y: Int): Int = {
      val d = x - y
      if (d > 0) x
      else y
    } ensuring(res => 
      x <= res && y <= res && (res == x || res == y))
  }

A Leon program consists of one or more modules delimited by
`object` and `class` declarations. 
The code of `max` attempts to compute maximum of two given arguments
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
However, Leon automatically finds that it is not correct,
showing us a counter-example inputs, such as 

.. code-block:: scala

  x -> -1639624704
  y -> 1879048192

We may wish to define a test method 

.. code-block:: scala

  def test4 = max(-1639624704, 1879048192)

whose evaluation indeed results in `ensuring` condition being violated.
The problem is due to overflow of 32-bit integers, due to which
the value `d` becomes positive, even though `x` is negative and thus smaller than
the large positive value `y`.
As in Scala, the `Int` type denotes 32-bit
integers with the usual signed arithmetic operations from
computer architecture and the JVM specification.

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

and then used as postcondition of `max` simply

.. code-block:: scala

  ensuring (res =>  res == rmax(x,y))

In general, Leon uses both function body and function
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
an arbitrary single invocation of a function. Leon is more likely to automatically
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
behavior of Leon.

In the sequel we will mostly use `BigInt` types.

Let us now look at synthesis. Suppose we omit
the implementation of `max`, keeping the specification
in the ensuring clause but using only a placeholder 
`???[BigInt]` indicating we are looking for an unknown implementation
of an integer type.

.. code-block:: scala

  def max(x: BigInt, y: BigInt): BigInt = {
    ???[BigInt]
  } ensuring(res => (res == x || res == y) &&  x <= res && y <= res)

Leon can then automatically generate an implementation that satisfies
this specification, such as 

.. code-block:: scala

  if (y <= x) {
    x
  } else {
    y
  }

This is remarkable because we have much more freedom in
writing specifications: we can explain the intention of the
computation using a conjunction of orthogonal properties,
and still obtain automatically an efficient implementation.

As a remark, an expression with missing parts in Leon is
an abbreviation for Leon's `choose` construct. Using `choose`
we can write the above example as

.. code-block:: scala

  def max(x: BigInt, y: BigInt): BigInt = choose((res:BigInt) => 
    (res == x || res == y) &&  x <= res && y <= res)

We explain `choose` in more detail through our subsequent examples.

Sorting Two Elements
--------------------

As a step towards sorting, let us specify a function that
sorts **two** mathematical integers. Here is what we need to
write.

.. code-block:: scala

  import leon.lang.Set
  import leon.lang.synthesis._
  object Sort {
    def sort2(x : BigInt, y : BigInt) = choose{(res: (BigInt,BigInt)) =>
      Set(x,y) == Set(res._1, res._2) && res._1 <= res._2
    }
  }

We use `import` to
include core constructs that are specific to Leon. Note
that, with the definitions in `leon._` packages, Leon
programs should also compile with the standard Scala
compiler. In that sense, Leon is a proper subset of Scala.

Our initial function that "sorts" two mathematical integers
is named `sort2`.  Namely, it accepts two arguments, `x` and
`y`, and returns a tuple, which we will here denote `res`,
which stores either `(x,y)` or `(y,x)` such that the first
component is less than equal the second component.

Note that we use `BigInt` to denote unbounded mathematical
integers. 

As usual in Scala, we write `res._1` for the first component
of the return tuple `res`, and `res._2` for the second
component of the tuple.

The specification says that the set of arguments is equal to
the set consisting of the returned tuple elements. The
notation `Set(x1,x2,...,xN)` denotes

.. math::

  \{ x_1, \ldots, x_N \}

that is, a finite set containing precisely the elements 
`x1`, `x2`,..., `xN`.

Finally, the `choose` construct takes a variable name (here,
`res`) denoting the value of interest and then gives, after
the `=>` symbol, a property that this value should
satisfy. We can read `choose{(x:T) => P}` as 

**choose x of type T such that P**

Here, we are interested in computing a result `res` tuple
such that the set of elements in the tuple is the same as
`{x,y}` and that the elements are in ascending order in the
tuple.  The specification thus describes sorting of lists of
length two.  Note that the result is uniquely specified, no
matter what the values of `x` and `y` are.

Evaluating exppressions containing choose
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Leon's built-in evaluator also works for `choose`
constructs.  To see it in action in the web interface, just
define a function without parameters, such as

.. code-block:: scala

    def testSort2 = sort2(30, 4)

Hovering over `testSort2` should display the computed result
`(4,30)`. (From :ref:`cmdlineoptions`, use `--eval`.)

Thanks to the ability to execute `choose` constructs Leon
supports programming with fairly general
constraints. Executing the `choose` construct is, however,
expensive. Moreover, the execution times are not very
predictable. This is why it is desirable to eventually
replace your `choose` constructs with more efficient
code. Leon can automate this process in some cases, using
**synthesis**.

Synthesizing Sort for Two Elements
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Instead of executing `choose` using a constraint solver
during execution, we can alternatively instruct Leon to
synthesize a function corresponding to `choose`.  The system
then synthesizes a computation that satisfies the
specification, such as, for, example:

.. code-block:: scala

  def sort2(x : BigInt, y : BigInt): (BigInt, BigInt) = {
    if (x < y)
      (x, y)
    else
      (y, x)
  }

Depending on the particular run, Leon may also produce a solution such as

.. code-block:: scala

  def sort2(x : BigInt, y : BigInt): (BigInt, BigInt) = {
    if (x < y) {
      (x, y)
    } else if (x == y) {
      (x, x)
    } else {
      (y, x)
    }
  }

This code performs some unnecessary case analysis, but still
satisfies our specification. In this case, the specification
of the program output is unambiguous, so all programs that
one can synthesize compute the same results for all inputs.

Remarks on Uniqueness
^^^^^^^^^^^^^^^^^^^^^

Let us give a name to the specification for `sort2`.

.. code-block:: scala

  def sort2spec(x: BigInt, y: BigInt, res: (BigInt, BigInt)): Boolean = {
    Set(x,y) == Set(res._1, res._2) && res._1 <= res._2
  }

We can then prove that the result is unique, by asking Leon
to show the following function returns `true` for all inputs
for which the `require` clause holds.

.. code-block:: scala

  def unique2(x: BigInt, y: BigInt, 
            res1: (BigInt, BigInt),
            res2: (BigInt, BigInt)): Boolean = {
    require(sort2spec(x,y,res1) && sort2spec(x,y,res2))
    res1 == res2
  }.holds

In contrast, if we define the corresponding specification for three integers

.. code-block:: scala

  def sort3spec(x: BigInt, y: BigInt, z: BigInt, res: (BigInt, BigInt, BigInt)): Boolean = {
    Set(x,y,z) == Set(res._1, res._2, res._3) && 
    res._1 <= res._2 && res._2 <= res._3
  }

Then uniqueness of the solution is the following conjecture:

.. code-block:: scala
  
  def unique3(x: BigInt, y: BigInt, z: BigInt, 
      res1: (BigInt, BigInt, BigInt),
      res2: (BigInt, BigInt, BigInt)): Boolean = {
    require(sort3spec(x,y,z,res1) && sort3spec(x,y,z,res2))
    res1 == res2
  }.holds

This time, however, Leon will report a counterexample, indicating
that the conjecture does not hold. One such counterexample is
0, 1, 1, for which the result (0, 0, 1) also satisfies the specification,
because sets ignore the duplicates, so 

.. code-block:: scala

    Set(x,y,z) == Set(res._1, res._2, res._2)

is true. This shows that writing specifications can be subtle, but Leon's
capabilities can help in the process as well.

**Question:** Write the specification that requires the output triple
to be strictly sorted using the `<` relation. Use `choose` to define
the corresponding `sort3` function.
Try executing such
specifications for example inputs. What happens if you execute it
when two of the elements are equal? Write the `require` clause
to enforce the precondition that the initial elements are distinct. 
Formulate in Leon the statement
that for triples of distinct elements the result of strictly ordering
them is unique and try to prove it.

Interactive Exploration of Program Space
----------------------------------------

For larger programs, the search may take too long to find
the solution and Leon will time out. In such cases, instead
of invoking automated search, you can invoke Leon in the
mode where the user directs each synthesis step to be
provided. This is a great way to understand the rules that
Leon currently has available for performing synthesis. 

In the `web interface`, select on the synthesis task for
`sort2` specification using the `choose` construct and
select `Explore` instead of the automated `Search`. You can
then navigate the space of programs interactively. Select
the `Inequality split` between the two input variables. The
system will apply this inference rule, and transform the
program with one `choose` into a program that performs case
analysis and then performs `choose` in each branch.  For
individual branches we can try to resolve them using the
`CEGIS` synthesis rule, which searches for small expressions
and tries to find the one that satisfies the specification.
We can use `Equivalent Inputs` and `Unused Inputs` as
needed, since they are generally a good idea to apply. Once
all sub-goals are resolved, select `Import Code`. Note
that you can import any of the intermediate steps in exploration:
the program with `choose` is valid in Leon, and it can even
be executed, thanks to run-time constraint solving for the
cases containing `choose`.

**Question:** Use interactive exploration to synthesize
`sort3` function by performing inequality splits in the
interactive interface.  Given three variables, you will
need to perform inequality splits on their pairs until
the tuple to be returned is known thanks to the tests
performed in the code. This is a somewhat tedious process,
but relatively easy, and the result is guaranteed to be
correct.

Defining Lists and Their Properties
-----------------------------------

We next consider sorting an unbounded number of elements.
For this purpose, we define a data structure for lists of
integers.  Leon has a built-in data type of parametric
lists, see :ref:`Leon Library <library>`, but here we define
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

As the starting point, we define size of a list.

.. code-block:: scala

    def size(l: List) : BigInt = (l match {
        case Nil => 0
        case Cons(x, rest) => 1 + size(rest)
    })

The definition uses *pattern matching* to define size of the
list in the case it is empty (where it is zero) and when it
is non-empty, or, if its non-empty, then it has a head `x`
and the rest of the list `rest`, so the size is one plus the
size of the rest. Thus `size` is a recursive function.  A
strength of Leon is that it allows using such recursive
functions in specifications.

It makes little sense to try to write a complete
specification of `size`, given that its recursive definition
is already a pretty clear description of its
meaning. However, it is useful to add a consequence of this
definition, namely that the size is non-negative. The reason
is that Leon most of the time reasons by unfolding `size`,
and the property of size being non-negative is not revealed
by such unfolding. Once specified, the non-negativity is
easily proven and Leon will make use of it.

.. code-block:: scala

    def size(l: List) : BigInt = (l match {
        case Nil => 0
        case Cons(x, rest) => 1 + size(rest)
    }) ensuring(res => res >= 0)


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

Consider the following specification of insertion into a sorted list,
which is a building block for an insertion sort.

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

Leon verifies that the returned list is indeed sorted. Note
how we are again using a recursively defined function to
specify another function. We can introduce a bug into the
definition above and examine the counterexamples that Leon
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
though in general it might be better in general to use bags
i.e. multisets).

.. code-block:: scala

  def content(l: List): Set[BigInt] = l match {
    case Nil => Set()
    case Cons(i, t) => Set(i) ++ content(t)
  }


Sorting Specification and Running It
------------------------------------

Specifying sorting is in fact very easy.

.. code-block:: scala

  def sortMagic(l : List) = {
     ???[List]
  } ensuring((res:List) => 
    isSorted(res) && content(res) == content(l))

We can execute such a sort.

.. code-block:: scala

  def mm = sortMagic(Cons(20, Cons(5, Cons(50, Cons(2, Nil)))))

obtaining the expected `Cons(2, Cons(5, Cons(20, Cons(50, Nil))))`.
Note that the function actually removes duplicates from the input list.

Synthesizing Sort
-----------------

By asking the system to synthesize the `choose` construct inside `magicSort`,
we may obtain a function such as the following, which gives
us the natural insertion sort.

.. code-block:: scala

    def sortMagic(l : List): List = {
      l match {
        case Cons(head, tail) =>
          sInsert(head, sortMagic(tail))
        case Nil => Nil
      }
    }

Going back and Synthesizing Insertion
-------------------------------------

In fact, if we have a reasonably precise enough
specification of insert, we can synthesize the implementation.
To try this, remove the body of `sInsert` and replace it
with `???[List]` denoting an unknown value of the given type.

.. code-block:: scala

  def sInsert(x : BigInt, l : List) : List = {
    require(isSorted(l))
    ???[List]
  } ensuring {(res:List) => 
     isSorted(res) && content(res) == content(l) ++ Set(x)}

Leon can then synthesize the missing part, resulting in a similar
body to the one we wrote by hand originally.

Repairing an Incorrect Function
-------------------------------

You may notice that synthesis can take a long time and fail.
Often we do produce some version of the program, but it is
not correct according to a specification.  Consider the
following attempt at `sInsert`.

.. code-block:: scala

  def sInsert(x : BigInt, l : List) : List = {
    require(isSorted(l))
    l match {
      case Nil => Cons(x, Nil)
      case Cons(e, rest) => Cons(e, sInsert(x,rest))
    }
  } ensuring {(res:List) => 
     isSorted(res) && content(res) == content(l) ++ Set(x)}

Leon reports a counterexample to the correctness. Instead of
trying to manually understand the counterexample, we can
instruct the system to **repair** this solution. If Leon can
reuse parts of the existing function, it can be much faster
than doing synthesis from scratch. Leon automatically finds
test inputs that it uses to localize the error and preserve
useful existing pieces of code. In this case, Leon repairs
the above function into the one equivalent to the original
one, by doing a case split and synthesizing two new cases,
resulting in the following equivalent function.

.. code-block:: scala

  def sInsert(x : BigInt, l : List): List = {
    require(isSorted(l))
    l match {
    case Nil => Cons(x, Nil)
    case Cons(e, rest) =>
      if (x < e) Cons(x, l)
      else if (x == e) Cons(x, rest)
      else Cons(e, sInsert(x, rest))
  } ensuring { (res : List) => 
    isSorted(res) && content(res) == content(l) ++ Set[BigInt](x) }


This completes the tutorial. To learn more, check the rest of this documentation and browse the examples provided with Leon.
