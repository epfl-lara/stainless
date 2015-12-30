.. _genc:

Safe C Code
===========

Leon can generate from Scala code an equivalent and safe C99 code. Using the verification, repair and
synthesis features of Leon this conversion can be made safely. Additionally, the produced code can be
compiled with any standard-compliant C99 compiler to target the desired hardware architecture
without extra dependencies.

To convert a Scala program, one can use the ``--genc`` and ``--o=<output.c>`` command line options
of Leon.

.. NOTE::
  Currently the memory model is limited to stack-allocated memory. Hence, no dynamic allocation
  is done using ``malloc`` function family.


Supported Features
------------------

The supported subset of Scala includes part of the core languages features, as well as some
extensions from :ref:`XLang <xlang>`, while ensuring the same expression execution order in both
languages.

Currently all type and function definitions need to be included in one top level object.


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
  * - ``Int`` (32-bit Integer)
    - ``int32_t``

Tuples
^^^^^^

Using ``TupleN[T1, ..., TN]`` results in the creation of a C structure with the same
fields and types for every combination of any supported type ``T1, ..., TN``. The name of the
generated structure will be unique and reflect the sequence of types.


Arrays
^^^^^^

``Array[T]`` are implemented using regular C array when the array size is known at compile time, or
using Variable Length Array (VLA) when the size is only available at runtime. Both types of array
use the same unique structure type to keep track of the length of the array and its allocated
memory.

.. NOTE::

  Arrays live on the stack and therefore cannot be returned by functions. This limitation is
  extended to other types having an array as field.


Arrays can be created using the companion object, e.g. ``Array(1, 2, 3)``, or using the
``Array.fill`` method, e.g. ``Array.fill(size)(value)``.


Case Classes
^^^^^^^^^^^^

The support for classes is restricted to non-recursive case classes for which fields are immutable.
Instances of such data-types live on the stack.


Functions
*********

Functions and nested functions are supported, with access to the variables in their respective
scopes. However, higher order functions are as of this moment not supported.

Since strings of characters are currently not available, to generate an executable program, one has
to define a main function without any argument that returns an integer: ``def main: Int = ...``.

Both ``val`` and ``var`` are supported with the limitations imposed by the :ref:`XLang <xlang>`
extensions.


Constructs
**********

The idiomatic ``if`` statements such as ``val b = if (x >= 0) true else false`` are converted into
a sequence of equivalent statements.

Imperative ``while`` loops are also supported.

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
  * - Arithmetic operators over integers
    - ``+``, ``-`` (unary & binary), ``*``, ``/``, ``%``
  * - Bitwise operators over integers
    - ``&``, ``|``, ``^``, ``~``, ``<<``, ``>>``


