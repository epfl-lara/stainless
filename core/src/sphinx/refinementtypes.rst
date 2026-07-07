.. _refinementtypes:

Refinement Types
================

Stainless supports *refinement types* as an additional way to provide specification.

Syntax
------

A refinement type is written using a brace-and-``with`` notation:

.. code-block:: scala

  { x: T with p(x) }

where ``x`` is a local binder, ``T`` is the parent type, and ``p(x)`` is a
boolean expression that may refer to ``x``.  For example:

.. code-block:: scala

  type Pos = { v: BigInt with v > 0 }
  type Even = { n: Int with n % 2 == 0 }
  type NonEmptyList[T] = { l: List[T] with l.nonEmpty }

In some cases we can use the shorthand notation for refinement types ``val x: Int with x > 0`` by reusing the name of the variable as the binder.  This is equivalent to ``val x: { v: Int with v > 0 }``.

Using Refinement Types in Function Signatures
---------------------------------------------

Refinement types are most useful on function parameters and return types. 

**Refined parameters** express preconditions directly in the type:

.. code-block:: scala

  def sqrt(x: { v: BigInt with v >= 0 }): BigInt = ???

**Refined return types** express postconditions directly in the type:

.. code-block:: scala

  def abs(x: BigInt): { r: BigInt with r >= 0 } =
    if x >= 0 then x else -x

A refined parameter ``x: { v: T with p(v) }``
is conceptually equivalent to adding ``require(p(x))`` at the top of the
function body.  Likewise, a refined return type ``{ r: T with q(r) }`` is
equivalent to ``.ensuring(r => q(r))``. You are free to use either style; the two can even be mixed.

Pattern Matching with Refinements
-----------------------------------

Refinements can appear as type patterns inside ``match`` expressions:

.. code-block:: scala

  type Pos = { i: Int with i > 0 }

  def classifySign(b: Boolean): Boolean =
    val v = if b then 42 else 0
    v match
      case p: Pos                         => true   // v > 0 branch
      case _: { i: Int with i == 0 }      => true   // v == 0 branch

Stainless checks that the patterns are exhaustive and that the refinement
predicates are consistent with what can be known about the scrutinee at each
branch.

Ghost Refinements
-----------------

Refinement predicates may refer to :doc:`ghost <ghost>` values and functions.
In the example below, ``valid`` is a ghost method used purely for
specification:

.. code-block:: scala

  import stainless.annotation.ghost
  import stainless.lang._

  case class ClassWithInvariant(var x: BigInt):
    @ghost
    def valid: Boolean = x >= 0

    def f(v: { v: BigInt with valid && v >= 0 }): { res: BigInt with valid } =
      x + v

Because ``valid`` is ghost, it is erased at run time.  The verification
obligation is still discharged by Stainless statically.

Semantics of Refinement Types (With Mutation)
----------------------------------------------

We assign refinement types the following semantics:

* A refinement type on a function's return type is equivalent to a postcondition on the function. For example:
 
   .. code-block:: scala

     def f(x: Int): { res: Int with res > 0 } = ???

   is equivalent to:

   .. code-block:: scala

     def f(x: Int): Int = ???
       .ensuring(res => res > 0)

  If the refinement type references mutable state, for example:

    .. code-block:: scala

      case class Box(var x: Int):
        def setX(y: Int): { res: Unit with x == y } =
          x = y

    then the postcondition is interpreted as ``.ensuring(_ => x == y)``, where ``x`` is the field's value after execution of ``setX``.

* A refinement type on a value is equivalent to an assertion on the value. For example:

   .. code-block:: scala

    val x: Int with x > y = y + 1

   is equivalent to:

   .. code-block:: scala

    val x: Int = y + 1
    assert(x > y)

  If the refinement type references mutable state, for example:

    .. code-block:: scala

      var y: Int = 4
      val x: Int with x > y = y + 1
      y = -1

  is equivalent to

    .. code-block:: scala

      var y: Int = 4
      val x: Int = y + 1
      assert(x > y)
      y = -1

* A refinement type on a ``var`` is understood as an invariant:

  .. code-block:: scala

    var x: Int with x > 0 = 1
    x = -1 // error: x > 0 is violated

  To maintain this invariant semantics, we disallow referencing mutable variables in refinement types of ``var`` declarations. For example, the following code is rejected: 

    .. code-block:: scala

      var x: Int = 1
      var y: Int with y > x = 2 // error: refinement type of y references mutable variable x


.. note::

  Side effects and mutation in refinement predicates are not allowed.

Good Patterns for Using Refinement Types
------------------------------------------

Several code patterns benefit from refinement types.

**Postconditions on abstract methods** are a natural fit. For example, consider this interface:

.. code-block:: scala

  trait Sorting:
    def sort[T : Ordering](xs: List[T]): List[T]

To express that ``sort``'s result is sorted without refinement types, we would write:

.. code-block:: scala

  trait Sorting:
    def sort[T : Ordering](xs: List[T]): List[T] =
      (??? : List[T])
    .ensuring(res => res.isSorted)

where ``???`` represents the unimplemented body. With refinement types, the postcondition becomes part of the return type:

.. code-block:: scala

  trait Sorting:
    def sort[T : Ordering](xs: List[T]): { l: List[T] with l.isSorted }

**Refined parameters in higher-order functions** help propagate constraints. Consider a ``toRoots`` function that applies ``squareRoot`` to each element:

.. code-block:: scala

  def toRoots(xs: List[Int]): List[Int] =
    xs.map(squareRoot)

  def squareRoot(i: Int): Int =
    require(i > 0)
    ???

For verification to succeed, we need to ensure all elements of the input list are positive. With refinement types, this constraint becomes part of the parameter's type:

.. code-block:: scala

  type Pos = { i: Int with i > 0 }

  def toRoots(xs: List[Pos]): List[Int] =
    xs.map(squareRoot)

``Pos`` is a zero-cost abstraction, as no wrapper object is created. Without refinement types, you would need to define a wrapper class and handle conversions throughout the code:

.. code-block:: scala

  case class Pos(i: Int):
    require(i > 0)

Setup with Refinement Types
----------------------------

Refinement types work out of the box with the latest version of Stainless. However, the Scala compiler requires a forked Dotty compiler (from the ``ch.epfl.lara`` organization) and two compiler flags:

- ``-language:experimental.qualifiedTypes`` — enables refinement type syntax
- ``-language:experimental.qualifiedTypes.silent`` — bypass Scala compiler checks for refinement types and defers them to Stainless

Both flags can be replaced with appropriate imports; see the `Scala documentation <https://nightly.scala-lang.org/docs/reference/experimental/index.html>`_ for details.

For example, the following ``build.sbt`` file sets up a project with refinement types:

.. code-block:: scala

  scalaOrganization := "ch.epfl.lara"
  scalacOptions ++= Seq("-language:experimental.qualifiedTypes", "-language:experimental.qualifiedTypes.silent")


.. note::

  This works with sbt 2.x and 1.12.4 and above. For earlier versions of sbt, a workaround is needed to obtain the correct compiler bridge. See `this comment <https://github.com/sbt/sbt/issues/8731#issuecomment-3967140035>`_ for details.

Limitations
-----------

* The Scala program must still type-check without refinement types. For example, the following code will not compile:

  .. code-block:: scala

    trait A
    case class B() extends A
    def foo(x: B): Unit = ()
    val x: { v: A with v.isInstanceOf[B] } = B()
    foo(x) // error: foo expects B, not A

  A workaround is to use a type cast, e.g. ``foo(x.asInstanceOf[B])``.  This is safe because Stainless verifies all type casts statically.

* Not all patterns expressible with ``require`` and ``.ensuring`` can be expressed with refinement types. For example, invariants on mutable fields cannot be captured:

  .. code-block:: scala

    case class Positions(var x: BigInt, var y: BigInt):
      require(x >= y)

  Attempting to express this as a refinement field:

  .. code-block:: scala

    case class Positions(var x: BigInt, var y: BigInt, val prop: Unit with x >= y)

  would treat the refinement as a constructor assertion, not as a maintained invariant on the mutable fields.