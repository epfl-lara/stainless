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

Stainless rejects programs in which an equality may compare values of
type ``Any``, directly or through the fields of a class, the components
of a tuple or the elements of a collection. Type parameters and abstract
type members are *equality types* by default: their values can be
compared with ``==``, and in exchange they can only be instantiated with
types that do not contain ``Any``. The ``@noeq`` annotation lifts this
restriction for a type parameter or type member whose values are never
compared, in the same way as ``@mutable`` allows mutable type arguments:

* ``==``, literal patterns, the elements of ``Set`` and ``Bag`` and the
  keys of ``Map`` cannot involve a type that contains ``Any`` or a
  ``@noeq`` type parameter or type member;
* a type parameter that is not ``@noeq`` (as ``T`` in
  ``def same[T](x: T, y: T) = x == y`` or in ``List[T]``) cannot be
  instantiated with such a type, and an abstract type member that is not
  ``@noeq`` cannot be defined as such a type;
* a method overriding a method with a ``@noeq`` type parameter must
  annotate the parameter as well.

As ``Any`` is also a mutable type for Stainless, a type parameter must be
both ``@noeq`` and ``@mutable`` to be instantiated with ``Any``:

.. code-block:: scala

  def first[@noeq @mutable T](x: T, y: T): T = x

  def test = first[Any](1, 2L) // ok: the values are not compared

Values of type ``Any`` remain supported as long as they are not
compared, for instance with ``isInstanceOf`` and pattern matching on
types. To compare such values, narrow them to a concrete type first.

For the same reason, a disagreement with the JVM, ``==`` is rejected on
a class that is not a case class (its values are compared by reference
on the JVM), such a class is treated like ``Any`` in the rules above,
and a class cannot override ``equals``. Lambdas can only be compared in
ghost code, also when they are reached through the fields of the
compared values.
