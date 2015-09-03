.. _xlang:

XLang
=====

To complement the core :ref:`Pure Scala <purescala>` language, the XLang module
of Leon brings a few extensions to that core language.

These extensions are kept as an optional feature, that needs to be explicitly
enabled from the command line with the option ``--xlang``. If you do not specify
the option, Leon will reject any program making use of an XLang feature.

On the technical side, these extensions do not have specific treatment in the
back-end of Leon. Instead, they are desugared into :ref:`Pure Scala <purescala>`
constructs during a preprocessing phase in the Leon front-end.

Imperative Code
---------------

XLang lets you introduce local variables in functions, and use Scala assignments
syntax.

.. code-block:: scala

   def foo(x: Int): Int = {
     var a = x
     var b = 42
     a = a + b
     b = a
     b
   }

The above example illustrates three new features introduced by XLang:

1. Declaring a variable in a local scope 

2. Blocks of expressions

3. Assignments

You can use Scala variables with a few restrictions. The variables can only be
declared and used locally in the same function, and inner functions cannot
close over them. XLang introduces the possibility to use sequences of
expressions (blocks) -- a feature not available in :ref:`Pure Scala
<purescala>`, where you're only option is a sequence of ``val`` which
essentially introduce nested ``let`` declarations.

.. warning::
   Be careful when combining variables with nested functions from PureScala. Leon
   will reject code with nested functions accessing a variable from an outside scope:
   
   .. code-block::  scala

      def foo(x: Int) = {
        var a = 12
        def bar(y: Int): Int = {
          a = a + 1
          a + y
        }
        bar(17)
      }

   The problem with such code is the complications involved in representing closures as
   they need a pointer to an environment containing the variables. Leon is only able
   to handle closures with ``val``, where it is sufficient to explicitly pass the values
   as parameters.


While loops 
***********

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

Leon will automatically generate a postcondition to the ``while`` loop, using
the negation of the loop condition. It will automatically prove that
verification condition and you should see an ``invariant postcondition`` marked
as ``valid``.

Leon internally handle loops as a function with a postcondition. For the end-user it
means that Leon is only going to rely on the postcondition of the loop to prove properties
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
``invariant`` a valid keyword. Leon is defining an implicit conversion from
``Unit`` to an ``InvariantFunction`` object that provides an ``invariant``
method. The ``invariant`` method takes a boolean expression as a parameter and
its semantics is to hold at the following points during the execution of the loop:

1. When first entering the loop: initialization.
2. After each complete execution of the body.
3. On exiting the loop.

Leon will generate verification conditions ``invariant inductive`` and
``invariant postcondition`` to verify points (2) and (3) above. It will also
generate a ``precondition`` corresponding to the line of the while loop. This
verification condition is used to prove the invariant on initialization of the
loop.

Arrays
******

PureScala supports functional arrays, that is, the operations ``apply`` and
``updated`` which do not modify an array but only returns some result. In
particular, ``updated`` returns a new copy of the array.

.. code-block:: scala

   def f(a: Array[Int]): Array[Int] = {
     a(0).updated(0, a(1))
   }

However, using functional arrays is not the most natural way to work with
arrays, and arrays are often used in imperative implementations of algorithms.
XLang adds the usual ``update`` operation on arrays:

.. code-block:: scala

   val a = Array(1,2,3,4)
   a(1) //2
   a(1) = 10
   a(1) //10

There are some limitations with what you can do with arrays. Leon simply
rewrite arrays using ``update`` operation as assignment of function arrays
using ``updated``.  This leverages the built-in algorithm for functional array
and rely on the elimination procedure for assignments. Concretely, it would
transform the above on the following equivalent implementation:

.. code-block:: scala

   var a = Array(1,2,3,4)
   a(1) //2
   a = a.updated(1, 10)
   a(1) //10

Then Leon would apply the same process as for any other XLang program.

Due to the way Leon handles side-effects, you cannot update arrays passed
to a function as a parameter.

Epsilon
-------

XLang introduces the ``epsilon`` keyword to express non-determinism. The
concept is inspired from `Hilbert's epsilon calculus
<http://en.wikipedia.org/wiki/Epsilon_calculus>`_. An ``epsilon`` expression
takes a predicate as parameter and is defined to return a value that
satisfies the predicate:

.. code-block:: scala

   def getInRange(from: Int, to: Int): Int = {
     epsilon(n => from <= n && n <= to)
   }

You can use epsilon when you only know the interface of some function but
cannot provide a concrete implementation.
