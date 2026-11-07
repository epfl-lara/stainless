.. _limitations:

Limitations of Verification
---------------------------

A goal of Stainless is to ensure that proven properties hold in
all program executions so that, for example, verified programs
do not crash and all of the preconditions and postconditions
are true in all executions.
For this to be the case, there needs
to be a precise correspondence between runtime execution
semantics and the semantics used in verification, including
the SMT solvers invoked. 

Below we document several cases where we are aware that the
discrepancy exists and provide suggested workarounds.

Out of Memory Errors
^^^^^^^^^^^^^^^^^^^^

By default, Stainless assumes that unbounded data types can
be arbitrarily large and that all well-founded recursive
functions have enough stack space to finish their computation.
Thus a verified program may crash at run-time due to:

  * stack overflow
  * heap overflow

The set of values for recursive algebraic data types is assumed to be infinite.
In any given execution, there will be actual bounds on the
total available memory. The program could thus crash
with an out-of-memory error when trying to allocate another
value of algebraic data type.

For a safety critical application you may wish to resort to
tail-recursive programs only, and also write preconditions
and postconditions that enforce a bound on the maximum size
of the data structures that your application
manipulates. For this purpose, you can define size functions
that return `BigInt` data types.

Equality on ``Any``
^^^^^^^^^^^^^^^^^^^

On the JVM, ``==`` between two values of static type ``Any`` compares
boxed numbers by value across numeric types, and compares boxed
floating-point numbers with IEEE semantics:

.. code-block:: scala

  val a: Any = (5: Byte)
  val b: Any = 5
  a == b // true on the JVM

Stainless encodes values of type ``Any`` with a structural equality in
which values of different types are never equal, so it would prove
``a != b`` and could therefore prove properties that do not hold at
runtime.

Stainless therefore compiles programs with Scala's `multiversal
equality <https://docs.scala-lang.org/scala3/reference/contextual/multiversal-equality.html>`_
enabled (``-language:strictEquality``): ``==`` and ``!=`` between
values of types ``L`` and ``R`` require a ``CanEqual[L, R]`` instance.
Scala provides instances for the primitive types, ``String``,
``BigInt`` and tuples of comparable types, and the Stainless library
provides them for its classes; the type arguments of ``List``, ``Set``,
``Map`` or ``Option`` must be comparable for their values to be. A user
class is made comparable with ``derives CanEqual``, which requires an
instance for each of its type arguments, and a function comparing
values of a type parameter ``T`` takes one as a context parameter:

.. code-block:: scala

  case class Box[T](x: T) derives CanEqual

  def same[T](x: T, y: T)(using CanEqual[T, T]): Boolean = x == y

There is no instance for ``Any``, so the comparison above as well as
``same[Any]``, ``Box[Any] == Box[Any]`` or ``List[Any].contains`` are
rejected by the compiler. Stainless adds two checks of its own: a class
deriving ``CanEqual`` cannot hold a value of type ``Any`` through its
fields, as the derivation only considers the type arguments, and a
number cannot be compared with a value of another kind that the JVM
compares by value (``BigInt``, ``Char``). ``CanEqual`` instances other
than the derived ones are not supported, except ``given CanEqual[X, X] =
CanEqual.derived`` for an opaque type ``X`` over a primitive type,
``String`` or ``BigInt``. The ``stainless.lang`` package provides
instances for function types, whose values can be compared in ghost
code only.

Values of type ``Any`` remain supported as long as they are not
compared, for instance with ``isInstanceOf`` and pattern matching on
types. To compare such values, narrow them to a concrete type first.
