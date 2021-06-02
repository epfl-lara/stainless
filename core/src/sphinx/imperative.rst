.. _imperative:

Imperative
==========

To complement the core :doc:`Pure Scala <purescala>` language, Stainless
proposes a few extensions to that core language.

On the technical side, these extensions do not have specific treatment in the
back-end of Stainless. Instead, they are desugared into :doc:`Pure Scala <purescala>`
constructs during a preprocessing phase in the Stainless front-end.

Imperative Code
---------------

Stainless lets you introduce local variables in functions, and use Scala assignments
syntax.

.. code-block:: scala

  def foo(x: Int): Int = {
    var a = x
    var b = 42
    a = a + b
    b = a
    b
  }

The above example illustrates three new features introduced by imperative support:

1. Declaring a variable in a local scope

2. Blocks of expressions

3. Assignments

You can use Scala variables with a few restrictions. The variables can only be
declared and used locally, no variable declaration outside of a function body.
There is also support for variables in case classes constructors. Imperative support
introduces the possibility to use sequences of expressions (blocks) -- a
feature not available in :doc:`Pure Scala <purescala>`, where your only
option is a sequence of ``val`` which essentially introduce nested ``let``
declarations.


While loops
-----------

You can use the ``while`` keyword. While loops usually combine the ability to
declare variables and make a sequence of assignments in order to compute
something useful:

.. code-block:: scala

  def foo(x: Int): Int = {
    var res = 0
    var i = 0
    while(i < 10) {
      res = res + i
      i = i + 1
    }
    res
  }

Stainless will automatically generate a postcondition to the ``while`` loop, using
the negation of the loop condition. It will automatically prove that
verification condition and you should see an ``invariant postcondition`` marked
as ``valid``.

Stainless internally handles loops as a function with a postcondition. For the end-user, it
means that Stainless is only going to rely on the postcondition of the loop to prove properties
of code relying on loops. Usually that invariant is too weak to prove anything remotely
useful and you will need to annotate the loop with a stronger invariant.

You can annotate a loop with an invariant as follows:

.. code-block:: scala

  var res = 0
  var i = 0
  (while(i < 10) {
    res = res + i
    i = i + 1
  }) invariant(i >= 0 && res >= i)

The strange syntax comes from some Scala magic in order to make the keyword
``invariant`` a valid keyword. Stainless is defining an implicit conversion from
``Unit`` to an ``InvariantFunction`` object that provides an ``invariant``
method. The ``invariant`` method takes a boolean expression as a parameter and
its semantics is to hold at the following points during the execution of the loop:

1. When first entering the loop: initialization.
2. After each complete execution of the body.
3. On exiting the loop.

Stainless will generate verification conditions ``invariant inductive`` and
``invariant postcondition`` to verify points (2) and (3) above. It will also
generate a ``precondition`` corresponding to the line of the while loop. This
verification condition is used to prove the invariant on initialization of the
loop.

Arrays
------

PureScala supports functional arrays, that is, the operations ``apply`` and
``updated`` which do not modify an array but only returns some result. In
particular, ``updated`` returns a new copy of the array.

.. code-block:: scala

  def f(a: Array[Int]): Array[Int] = {
    a.updated(0, a(1))
  }

However, using functional arrays is not the most natural way to work with
arrays, and arrays are often used in imperative implementations of algorithms.
We add the usual ``update`` operation on arrays:

.. code-block:: scala

  val a = Array(1,2,3,4)
  a(1) //2
  a(1) = 10
  a(1) //10

Stainless simply rewrite arrays using ``update`` operation as the assignment of function arrays
using ``updated``.  This leverages the built-in algorithm for functional arrays
and relies on the elimination procedure for assignments. Concretely, it would
transform the above on the following equivalent implementation:

.. code-block:: scala

  var a = Array(1,2,3,4)
  a(1) //2
  a = a.updated(1, 10)
  a(1) //10

Stainless also has a ``swap`` operation in ``stainless.lang``, which is equivalent to two updates.

.. code-block:: scala

  def swap[@mutable T](a1: Array[T], i1: Int, a2: Array[T], i2: Int): Unit


Mutable Objects
---------------

A restricted form of mutable classes is supported via case classes with ``var``
arguments:

.. code-block:: scala

  case class A(var x: Int)
  def f(): Int = {
    val a = new A(10)
    a.x = 13
    a.x
  }

Mutable case classes are behaving similarly to ``Array``, and are handled with a
rewriting, where each field updates becomes essentially a copy of the object with
the modified parameter changed.

Aliasing
--------

With mutable data structures comes the problem of aliasing. In Stainless, we
maintain the invariant that in any scope, there is at most one pointer to some
mutable structure. Stainless will issue an error if you try to create an alias to
some mutable structure in the same scope:

.. code-block:: scala

  val a = Array(1,2,3,4)
  val b = a //error: illegal aliasing
  b(0) = 10
  assert(a(0) == 10)

However, Stainless correctly supports aliasing mutable structures when passing it
as a parameter to a function (assuming its scope is not shared with the call
site, i.e. not a nested function). Essentially you can do:

.. code-block:: scala

  case class A(var x: Int)
  def updateA(a: A): Unit = {
    a.x = 14
  }
  def f(): Unit = {
    val a = A(10)
    updateA(a)
    assert(a.x == 14)
  }

The function ``updateA`` will have the side effect of updating its argument
``a`` and this will be visible at the call site.

Annotations for Imperative Programming
--------------------------------------

We introduce the special function ``old`` that can be used in postconditions to
talk about the value of a variable before the execution of the block. When you refer to a variable
or mutable structure in a post-condition, Stainless will always consider the current value of
the object, so that in the case of a post-condition this would refer to the final value of the
object. Using ``old``, you can refer to the original value of the variable and check some
properties:

.. code-block:: scala

  case class A(var x: Int)
  def inc(a: A): Unit = {
    a.x = a.x + 1
  } ensuring(_ => a.x == old(a).x + 1)

``old`` can be wrapped around any identifier that is affected by the body. You can also use
``old`` for variables in scope, in the case of nested functions:

.. code-block:: scala

  def f(): Int = {
    var x = 0
    def inc(): Unit = {
      x = x + 1
    } ensuring(_ => x == old(x) + 1)

    inc(); inc();
    assert(x == 2)
  }

Trait Variables
---------------

Traits are allowed to declare variables, with the restriction that these cannot be
assigned a default value.

.. code-block:: scala

  trait MutableBox[A] {
    var value: A
  }

Such abstract variables must be overridden at some point by either:

a) a mutable field of a case class

.. code-block:: scala

  case class Box[A](var value: A) extends MutableBox[A]

b) a pair of getter/setter

.. code-block:: scala

  case class WriteOnceBox[A](
    var underlying: A,
    var written: Boolean = false
  ) extends MutableBox[A] {

    def value: A = underlying

    def value_=(newValue: A): Unit = {
      if (!written) {
        underlying = newValue
        written = true
      }
    }
  }

Note: a setter is not required to actually perform any mutation, and the following
is a perfectly valid sub-class of `MutableBox`:

.. code-block:: scala

  case class ImmutableBox[A](underlying: A) extends MutableBox[A] {
    def value: A = underlying
    def value_=(newValue: A): Unit = ()
  }


Return keyword
--------------

Stainless partially supports the `return` keyword. For verification, an internal
phase of Stainless (called `ReturnElimination`) injects a data-structure named
`ControlFlow` to simulate the control flow of programs with returns.

.. code-block:: scala

  sealed abstract class ControlFlow[Ret, Cur]
  case class Return[Ret, Cur](value: Ret)  extends ControlFlow[Ret, Cur]
  case class Proceed[Ret, Cur](value: Cur) extends ControlFlow[Ret, Cur]

Here is a function taken from `ControlFlow2.scala <https://github.com/epfl-lara/stainless/blob/master/frontends/benchmarks/imperative/valid/ControlFlow2.scala>`_:

.. code-block:: scala

  def foo(x: Option[BigInt], a: Boolean, b: Boolean): BigInt = {
    if (a && b) {
      return 1
    }

    val y = x match {
      case None()       => return 0
      case Some(x) if a => return x + 1
      case Some(x) if b => return x + 2
      case Some(x)      => x
    };

    -y
  }

The program transformation can be inspected by running:

  .. code-block:: bash

    stainless ControlFlow2.scala --batched --debug=trees --debug-objects=foo --debug-phases=ReturnElimination

We get the following output (with ``cf`` identifiers renamed for clarity; you can
use the ``--print-ids`` option so that Stainless expressions get displayed with
unique identifiers, at the cost of readability):

  .. code-block:: scala

    def foo(x: Option[BigInt], a: Boolean, b: Boolean): BigInt = {
      val cf0: ControlFlow[BigInt, Unit] = if (a && b) {
        Return[BigInt, Unit](1)
      } else {
        Proceed[BigInt, Unit](())
      }
      cf0 match {
        case Return(retValue) =>
          retValue
        case Proceed(proceedValue) =>
          val cf1: ControlFlow[BigInt, BigInt] = x match {
            case None()       => Return[BigInt, BigInt](0)
            case Some(x) if a => Return[BigInt, BigInt](x + 1)
            case Some(x) if b => Return[BigInt, BigInt](x + 2)
            case Some(x)      => Proceed[BigInt, BigInt](x)
          }
          cf1 match {
            case Return(retValue) =>
              retValue
            case Proceed(proceedValue) =>
              -proceedValue
          }
      }
    }

Stainless also supports ``return`` in while loops, and transforms them to local functions, also in
the ``ReturnElimination`` phase. Here is a function taken from `ReturnInWhile.scala <https://github.com/epfl-lara/stainless/blob/master/frontends/benchmarks/imperative/valid/ReturnInWhile.scala>`_.

  .. code-block:: scala

    def returnN(n: Int): Int = {
      require(n >= 0)
      var i = 0
      (while (true) {
        decreases(n - i)
        if (i == n) return i
        i += 1
      }).invariant(0 <= i && i <= n)

      assert(false, "unreachable code")
      0
    }.ensuring((res: Int) => res == n)

After transformation, we get a recursive (local) function named ``returnWhile``
that returns a control flow element to indicate whether the loop terminated
normally or returned. We check that the invariant clause of the while loop is
indeed an invariant by adding it to the pre and postconditions of the generated
``returnWhile`` function. When the while loop returns, we check in addition that
the postcondition of the top-level holds (see comment).

  .. code-block:: scala

    def returnN(n: Int): Int = {
      require(n >= 0)

      var i: Int = 0
      val cf0: ControlFlow[Int, Unit] = {
        def returnNWhile: ControlFlow[Int, Unit] = {
          require(0 <= i && i <= n)
          decreases(n - i)
          {
            val cf1: ControlFlow[Int, Unit] = if (i == n) {
              Return[Int, Unit](i)
            } else {
              Proceed[Int, Unit](())
            }
            cf1 match {
              case Return(retValue) => Return[Int, Unit](retValue)
              case Proceed(proceedValue) =>
                Proceed[Int, Unit]({
                  i = (i + 1)
                  ()
                })
            }
          } match {
            case Return(retValue) =>
              Return[Int, Unit](retValue)
            case Proceed(proceedValue) =>
              if (true) {
                returnNWhile
              } else {
                Proceed[Int, Unit](())
              }
          }
        } ensuring {
          (cfWhile: ControlFlow[Int, Unit]) => cfWhile match {
            case Return(retValue) =>
              // we check the postcondition `retValue == n` of the top-level function
              retValue == n &&
              0 <= i && i <= n
            case Proceed(proceedValue) =>
              ¬true && 0 <= i && i <= n
          }
        }
        if (true) {
          returnNWhile
        } else {
          Proceed[Int, Unit](())
        }
      }
      cf0 match {
        case Return(retValue) => retValue
        case Proceed(proceedValue) =>
          assert(false, "unreachable code")
          0
      }
    } ensuring {
      (res: Int) => res == n
    }

Finally, ``return`` is also supported for local function definitions, with the same transformation.
It is however not supported for anonymous functions.
