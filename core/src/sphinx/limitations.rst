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
of a tuple, the elements of a collection or a type parameter:

* ``==``, literal patterns, the elements of ``Set`` and ``Bag`` and the
  keys of ``Map`` cannot involve a type that contains ``Any``;
* a type parameter whose values are compared with ``==`` (as in
  ``def same[T](x: T, y: T) = x == y`` or in ``List.contains``) cannot
  be instantiated with a type that contains ``Any``;
* an abstract type member whose values are compared with ``==`` cannot
  be defined as a type that contains ``Any``.

Which type parameters and type members have their values compared is
not declared but inferred: Stainless runs a whole-program analysis that
finds every ``==``, literal pattern and collection key, follows the type
parameters they involve through calls, class hierarchies and structural
equality until a fixpoint, and then rejects the instantiations of these
parameters with types that contain ``Any``. An instantiation is thus
rejected because of a comparison that may be far from it, in another
function or in the library, and the error message names that comparison
(``List[Any]`` is rejected because of ``List.contains``).

Values of type ``Any`` remain supported as long as they are not
compared, for instance with ``isInstanceOf`` and pattern matching on
types. To compare such values, narrow them to a concrete type first.
