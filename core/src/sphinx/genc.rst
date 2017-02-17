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

The input program can use types and functions defined in other units; Leon will scan each dependency
in turn starting from the main unit. It is therefore mandatory that every dependency use exclusively
supported features to allow the conversion to succeed.

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

Additionally, GenC has a partial support for character and string literals made of ASCII characters
only but it has no API to manipulate strings at the moment: `Char` is map to `char` and `String` is
map to `char*`.

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

Since strings of characters are currently not (fully) available, in order to generate an executable
program, one has to define a main function without any argument, that can optionally return an
integer, as follows: ``def _main(): Int = ...``. Moreover, an extern ``main`` function of the
following form is required in order to preserve the executability of the Scala program:

.. code-block:: scala

    @extern
    def main(args: Array[String]): Unit = _main()



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


Custom Conversion
-----------------

When it comes to function using system calls, such as I/Os, no automated conversion is possible. In
those situations the user can define his own implementation for functions, add manual conversion
from Scala types to C types or even drop some functions and types from the translation, with
``@cCode.function``, ``@cCode.typedef`` and ``@cCode.drop`` annotations from the package
``leon.annotation``, respectively. Their usage is described below.


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

Similarly to Scala's ``scala.io.StdIn`` and ``scala.io.StdOut``, Leon provides ``leon.io.StdIn`` and
``leon.io.StdOut``. These two APIs are provided with equivalent C code for easy translation with
GenC, but are also shaped to allow users to write proofs in a non-deterministic environment.

.. NOTE::

    Because these APIs are expected to evolve in the near future they are not reported here. Please
    refer to ``libary/leon/io/Std{In,Out}.scala`` more for details.


Furthermore, Leon provides ``leon.io.FileOutputStream`` to write data to a file with a C99
compatible API:

.. code-block:: scala


    object FileOutputStream {

      /**
       * Open a new stream to write into `filename`, erasing any previous
       * content of the file or creating a new one if needed.
       **/
      def open(filename: String): FileOutputStream

    }

    case class FileOutputStream(/** implementation details **/) {

      /**
       * Close the stream; return `true` on success.
       *
       * NOTE The stream must not be used afterward, even on failure.
       **/
      def close(): Boolean

      /**
       * Test whether the stream is opened or not.
       *
       * NOTE This is a requirement for all write operations.
       **/
      def isOpen(): Boolean

      /**
       * Append an integer to the stream and return `true` on success.
       *
       * NOTE The stream must be opened first.
       **/
      def write(x: Int): Boolean

      /**
       * Append a character to the stream and return `true` on success.
       *
       * NOTE The stream must be opened first.
       **/
      def write(c: Char): Boolean

      /**
       * Append a string to the stream and return `true` on success.
       *
       * NOTE The stream must be opened first.
       **/
      def write(s: String): Boolean

    }


.. NOTE::

    It is important that you close the stream after it was created or your C application might leak
    resources.


Similarly, Leon provides ``leon.io.FileInputStream`` to read data from a file with a C99
compatible API.


.. NOTE::

    Because this API is expected to evolve in the near future it is not reported here. Please
    refer to ``libary/leon/io/FileInputStream.scala`` for more details.

