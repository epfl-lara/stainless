.. _genc:

Generating C Code
=================

Stainless can generate from Scala code an equivalent and safe C99 code. Using the verification, repair and
synthesis features of Stainless this conversion can be made safely. Additionally, the produced code can be
compiled with any standard-compliant C99 compiler to target the desired hardware architecture
without extra dependencies. The initial description of GenC, which has evolved since then, can be found in `Extending Safe C Support In Leon
<https://infoscience.epfl.ch/record/227942/files/Extending%20Safe%20C%20Support%20In%20Leon.pdf>`_.
Furthermore, this Master Thesis Report explains how to achieve compliance under the `MISRA C
<https://en.wikipedia.org/wiki/MISRA_C>`_ guidelines.

To convert a Scala program, please use the ``--genc`` option of Stainless.

The option ``--genc-output=file`` specifies the file name for GenC output (default: ``stainless.c``).


.. NOTE::
  Currently the memory model is limited to stack allocation and global state. Hence, no dynamic allocation
  is done using ``malloc`` function family.


Requirements
------------

The following is required from the Scala program fed to GenC:

 - Functions compiled to C, and the types they use,
   should be exclusively in the set of features described below, with the
   exceptions of the (ghost) code used for verification conditions;

 - The program should be successfully verified with the ``--strict-arithmetic`` (enabled by default)
   flag to ensure that arithmetic operations, array accesses, function
   preconditions and so on, are safely converted into C code.


The generated C code should be compiled with a C99-compliant compiler that
satisfies these extra conditions:

 - ``CHAR_BITS`` is defined to be 8;

 - The ``int8_t``, ``int16_t``, ``int32_t``, ``int64_t`` and ``uint8_t``, ``uint16_t``, ``uint32_t``, ``uint64_t`` types are available (see :doc:`Pure Scala <purescala>` for description);

 - Casting from unsigned to signed integer, and vice-versa, is not well supported at the moment.


Export
------

Functions and classes can be marked with ``@cCode.export`` (``import stainless.annotation._``), 
which affects GenC compilation in several ways.
First, the names of these functions and classes will not get mangled when generating the C code.
Second, the signatures of the functions, and the type definitions corresponding to exported classes,
will go into the header file (by default ``stainless.h``).
Finally, preconditions of exported functions (which are meant to be called from external C code),
are transformed into runtime assertions.

Supported Features
------------------

The supported subset of Scala includes part of the core languages features, as well as some
imperative features, while ensuring the same expression execution order in both
languages.


Types
*****

The following raw types and their corresponding literals are supported:

.. list-table::
  :header-rows: 1

  * - Scala
    - C99
  * - ``Unit``
    - ``void``
  * - ``Boolean``
    - ``bool``
  * - ``Byte`` and ``Int8`` (8-bit integer)
    - ``int8_t``
  * - ``Short`` and ``Int16`` (16-bit integer)
    - ``int16_t``
  * - ``Int`` and ``Int32`` (32-bit integer)
    - ``int32_t``
  * - ``Long`` and ``Int64`` (64-bit integer)
    - ``int64_t``
  * - ``UInt8`` (8-bit unsigned integer)
    - ``uint8_t``
  * - ``UInt16`` (16-bit integer)
    - ``uint16_t``
  * - ``UInt32`` (32-bit integer)
    - ``uint32_t``
  * - ``UInt64`` (64-bit integer)
    - ``uint64_t``

Additionally, GenC has partial support for character and string literals made
of ASCII characters only but it has no API to manipulate strings at the moment:
``Char`` is mapped to ``char`` and ``String`` is mapped to ``char*``.

Tuples
^^^^^^

Using ``TupleN[T1, ..., TN]`` results in the creation of a C structure with the
same fields and matching types for every combination of any supported type
``T1, ..., TN``. The name of the generated structure will be unique and reflect
the sequence of types.


Arrays
^^^^^^

Arrays are compiled by GenC into C structs that also store the length of the array.
For ``Array[Int]`` we get:

.. code-block:: C

  typedef struct {
    int32_t* data;
    int32_t length;
  } array_int32;

.. NOTE::

  Arrays live on the stack and therefore cannot be returned by functions. This limitation is
  extended to other types having an array as field. In some cases, it is acceptable to use the
  ``@cCode.inline`` annotation from Stainless's library to workaround this limitation.

For case classes containing arrays whose length is known at compile time, we avoid
using a ``struct`` wrapper for the array, and instead directly inline the array
in the ``struct`` of the case class. We trigger this optimized transformation
when the array length is specified in the case class invariant (with ``require``)
as a conjunct. The left-hand-side needs to be ``a.length`` where ``a`` is the
array, and the right-hand-side needs to be a constant (or evaluate to a constant
at compile time).

See below for a case class with a fixed length array and its transformation in C:

.. code-block:: scala

  val CONSTANT1: UInt16 = 5
  val CONSTANT2: UInt16 = 12
  val CONSTANT3: UInt16 = CONSTANT1 + CONSTANT2

  @cCode.export
  case class W(x: Int, a: Array[Int], y: Int) {
    require(
      a.length == CONSTANT3.toInt &&
      0 <= x && x <= 1000 &&
      0 <= y && y <= 1000
    )
  }

.. code-block:: C

  typedef struct {
    int32_t x;
    int32_t a[17];
    int32_t y;
  } W;

Classes
^^^^^^^

The support for classes is restricted to non-recursive ones so that instances
of such data-types live on the stack. The following language features are available:

  - ``case class`` with mutable ``var`` fields;

  - generics:

    + similarly to ``Array[T]`` or tuples, each combination of type parameters
      is mapped to a specific C structure;

  - inheritance:

    + when all leaf classes have no fields, the class hierarchy is mapped to a
      C enumeration,

    + otherwise, a tagged-union is used to represent the class hierarchy in C;

  - external types:

    + see ``@cCode.typedef`` below.


Functions
*********

Functions with access to the variables in their respective scopes.  The
following language features are available:

  - top level, nested or member functions:

    + both ``val`` and ``var`` are supported for local variable with the limitations imposed by
      the imperative phases of Stainless

  - generics:

    + each combination of type parameters generates a different, specialised C function;

  - overloading:

    + the Scala compiler is responsible for identifying the correct function at each call site;

  - higher-order functions:

    + named functions that do not capture their environment can be used as value;

  - external functions:

    + see ``@cCode.function`` below;

Since strings of characters are currently not (fully) available, in order to generate an executable
program, one has to define a main function without any argument, whose return type can be ``Int``
or ``Unit``:

.. code-block:: scala

    @cCode.export
    def main(): Unit = {
      // main code goes here
    }


Constructs
**********

The idiomatic ``if`` statements such as ``val b = if (x >= 0) true else false`` are converted into
a sequence of equivalent statements.

Imperative ``while`` loops are also supported.

*Pattern matching* is supported, with the exception of the *Unapply
Patterns*, as long as it is exempt of side effect.

Assertions, invariant, pre- and post-conditions are not translated into C99 and are simply ignored.


Operators
*********

The following operators are supported:

.. list-table::
  :header-rows: 1

  * - Category
    - Operators
  * - Boolean operators
    - ``&&``, ``||``, ``!``, ``!=``, ``==``
  * - Comparision operators over integers
    - ``<``, ``<=``, ``==``, ``!=``, ``>=``, ``>``
  * - Comparision operators over instances of classes
    - ``==``, ``!=``
  * - Arithmetic operators over integers
    - ``+``, ``-`` (unary & binary), ``*``, ``/``, ``%``
  * - Bitwise operators over integers
    - ``&``, ``|``, ``^``, ``~``, ``<<``, ``>>>``


Global State
------------

At the moment, Stainless does not support global mutable variables declared in objects.
It is however possible to simulate global state by using classes marked with ``@cCode.global``,
as shown in the `Global.scala
<https://github.com/epfl-lara/stainless/blob/master/frontends/benchmarks/genc/Global.scala>`_
example:

.. code-block:: scala

  @cCode.global
  case class GlobalState(
    val data: Array[Int] = Array.fill(100)(0),
    var stable: Boolean = true,
    var x: Int = 5,
    var y: Int = 7,
  ) {
    require(
      data.length == 100 && (
        !stable || (
          0 <= x && x <= 100 &&
          0 <= y && y <= 100 &&
          x + y == 12
        )
      )
    )
  }

.. note::

  In classes annotated with ``@cCode.global``, only arrays with a fixed length are
  allowed. Please check the paragraph about arrays to learn how to specify the array length.

This annotation triggers some checks to make sure that indeed the ``GlobalState`` class
(the name of the class can be changed, and there can be multiple such classes) is used as a global
state:

* Functions can take as argument at most one instance per each global class such as ``GlobalState``.
* There can be at most one instance created for each global class such as ``GlobalState``
  (in a function that doesn't already take an instance of that class as argument).
* A ``GlobalState`` instance can only be used for reads and assignments (e.g. it cannot be let bound, except for the declaration mentioned above).
* The only global state that can be passed to other functions is the one we create or the one we received as a function argument.

These checks ensure that the fields of ``GlobalState`` can be compiled as global variables in ``C``.
Consider the ``move`` function from the `Global.scala
<https://github.com/epfl-lara/stainless/blob/master/frontends/benchmarks/genc/Global.scala>`_
example:

.. code-block:: scala

  def move()(implicit state: GlobalState): Unit = {
    require(state.stable && state.y > 0)
    state.stable = false
    state.x += 1
    state.y -= 1
    state.data(state.y) = 1
    state.stable = true
    if (state.y > 0) move()
  }.ensuring(_ => state.stable)

After compilation to C, we get the following function, with global declarations
``stable``, ``x``, ``y``, and ``data``.

.. code-block:: C

  int32_t data[100] = { 0 };
  bool stable = true;
  int32_t x = 5;
  int32_t y = 7;

  void move() {
      stable = false;
      x = x + 1;
      y = y - 1;
      data[y] = 1;
      stable = true;
      if (y > 0) {
          move();
      }
  }

Note that the initial values for the global variables correspond to the default values given
in the Stainless class declaration (default values are mandatory when using the ``@cCode.global``
annotation). When creating a global state instance (the only one), we do not pass arguments, to
make sure that the instance is created using the default values:

.. code-block:: scala

  @cCode.export
  def main() {
    implicit val gs = GlobalState()
    StdOut.print(gs.x)
    StdOut.print(gs.y)
    move()
    StdOut.print(gs.data(6))
    StdOut.print(gs.data(7))
    StdOut.print(gs.x)
    StdOut.println(gs.y)
  }

Stainless supports two variants of the ``@cCode.global`` annotation, namely ``@cCode.globalUninitialized``
and ``@cCode.globalExternal``. The first one generates global declarations without initial
values. These global variables are thus initialized according to C semantics, and there can be
a mismatch between the global state instance created by the user, and the initial values in C.
The second one hides the global declarations, which can be useful when interacting with C code
that declares global variables outside of the Stainless program.


Custom Conversion
-----------------

When it comes to function using system calls, such as I/Os, no automated conversion is possible. In
those situations the user can define his own implementation for functions, add manual conversion
from Scala types to C types or even drop some functions and types from the translation, with
``@cCode.function``, ``@cCode.typedef`` and ``@cCode.drop`` annotations from the package
``stainless.annotation``. Their usage is described below.


Custom Function Implementation
******************************

In order to circumvent some current limitations of GenC, one can use ``@cCode.function(code,
includes)`` to define the corresponding implementation of any top-level function or method, usually
accompanied by ``@extern``. Its usage is as follows:

  * For convenience, the C implementation generated by ``code`` is represented using a String and
    not an Abstract Syntax Tree. The user is responsible for the correctness of the provided C99
    code.  Because GenC might rename the function, e.g. to deal with overloading, the special
    ``__FUNCTION__`` token should be used instead of the original name. Furthermore, the parameters
    and return type should match the signature automatically generated by GenC.

  * The optional parameter ``includes`` can hold a colon separated list of required C99 include
    header files.

Here is a typical example:

.. code-block:: scala

    // Print a 32-bit integer using the *correct*
    // format for printf in C99
    @cCode.function(
      code = """
        | void __FUNCTION__(int32_t x) {
        |  printf("%"PRIi32, x);
        | }
        """,
      includes = "inttypes.h:stdio.h"
    )
    def myprint(x: Int): Unit = {
      print(x)
    }


Custom Type Translation
***********************

When a whole type need to be represented using a special C type, the ``@cCode.typedef(alias,
include)`` annotation can be used. Here the ``include`` parameter is also optional, however it can
only refer to one header, as it is not expected to have a type defined in several headers. The
``alias`` string must represent an existing and valid type.

Using an aliasing from ``S`` to ``C`` implies that every function that accept a ``S`` in the input
program must accept a ``C`` in the generated C code. Usually, using this annotation implicates
manually defining the implementation of functions using this type with ``@cCode.function``.

Here is an example:

.. code-block:: scala

    @cCode.typedef(alias = "FILE*", include = "stdio.h")
    case class MyFile( ...


Ignore Function or Type
***********************

It is also possible to skip the translation of some functions or types that are only used as
implementation details in proofs, for example, using the ``@cCode.drop()`` annotation.


API For Safe Low Level Programs
-------------------------------

In this section we describe the APIs that can be used to make the bridge between some Scala
programming facilities and their low level, equivalent, C features.


I/Os
****

Similarly to Scala's ``scala.io.StdIn`` and ``scala.io.StdOut``, Stainless provides ``stainless.io.StdIn`` and
``stainless.io.StdOut``. These two APIs are provided with equivalent C code for easy translation with
GenC, but are also shaped to allow users to write proofs in a non-deterministic environment.


Furthermore, Stainless provides ``stainless.io.FileInputStream`` to read data and
``stainless.io.FileOutputStream`` to write data to a file with a C99 compatible API.

.. NOTE::

    It is important that you close the stream after it was created or your C
    application might leak resources.
