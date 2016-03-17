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
declared and used locally, no variable declaration outside of a function body.
There is also support for variables in case classes constructors. XLang
introduces the possibility to use sequences of expressions (blocks) -- a
feature not available in :ref:`Pure Scala <purescala>`, where you're only
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
------

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

Leon simply rewrite arrays using ``update`` operation as assignment of function arrays
using ``updated``.  This leverages the built-in algorithm for functional array
and rely on the elimination procedure for assignments. Concretely, it would
transform the above on the following equivalent implementation:

.. code-block:: scala

   var a = Array(1,2,3,4)
   a(1) //2
   a = a.updated(1, 10)
   a(1) //10

Then Leon would apply the same process as for any other XLang program.

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

With mutable data structures comes the problem of aliasing. In Leon, we
maintain the invariant that in any scope, there is at most one pointer to some
mutable structure. Leon will issue an error if you try to create an alias to
some mutable structure in the same scope:

.. code-block:: scala

   val a = Array(1,2,3,4)
   val b = a //error: illegal aliasing
   b(0) = 10
   assert(a(0) == 10)

However, Leon correctly supports aliasing mutable structures when passing it
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

XLang introduces the special function ``old`` that can be used in postconditions to
talk about the value of a variable before the execution of the block. When you refer to a variable
or mutable structure in a post-condition, leon will always consider the current value of
the object, so that in the case of a post-condition this would refer to the final value of the
object. Using ``old``, you can refer to the original value of the variable and check some
properties:

.. code-block:: scala
   
   case class A(var x: Int)
   def inc(a: A): Unit = {
     a.x = a.x + 1
   } ensuring(_ => a.x == old(a).x + 1)

``old`` can be wrapped around any identifier that is affected by the body. You can also use
``old`` for variables in scope, in case of nested functions:

.. code-block:: scala
   
   def f(): Int = {
     var x = 0
     def inc(): Unit = {
       x = x + 1
     } ensuring(_ => x == old(x) + 1)

     inc(); inc();
     assert(x == 2)
   }


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
