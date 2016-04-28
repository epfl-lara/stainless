.. _faq:

Frequently Asked Questions
==========================

If you have a question, we suggest you post it at http://stackoverflow.com
(try `searching for the leon tag <http://stackoverflow.com/questions/tagged/leon?sort=newest>`_)
or contact one of the authors of this documentation.

Below we collect answers to some questions that came up.

Proving properties of size
^^^^^^^^^^^^^^^^^^^^^^^^^^

I have defined a size function on my algebraic data type.

.. code-block:: scala

  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case object Nil extends List
  def size(l: List) : Int = (l match {
    case Nil => 0
    case Cons(_, t) => 1 + size(t)
  }) ensuring(_ >= 0)

Leon neither proves nor gives a counterexample. Why?

**Answer:** You should consider using `BigInt`, which
denotes unbounded mathematical integers, instead of `Int`,
which denotes 32-bit integers. If you replace `Int` with
`BigInt` in the result type of `size`, the function should
verify. Note that algebraic data types can be arbitrarily
large, so, if the input list had the size `Int.MaxValue + 1`
(which is 2^32) then the addition `1 + size(t)` would wrap
around and produce `Int.MinValue` (that is, -2^31), so the
`ensuring` clause would not hold.

Use variable number of arguments in Leon programs
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

I have defined an apply function that should accept a variable number of arguments.

.. code-block:: scala

    import leon.collection._
    case class Element(children: List[Element]) {
      def addChildren(c: Element*): Element = {
        Element(children ++ c.toList)
      }
    }

This does not compile in Leon, why?

**Answer:** 

To support variable number of arguments, do the following:

.. code-block:: scala

    import leon.collection._
    import leon.annotation._
    case class Element(children: List[Element]) {
      @ignore
      def addChildren(c: Element*): Element = {
        var l: List[WebTree] = Nil[WebTree]()
        for (e <- elems) {
          l = Cons(e, l)
        }
        addChildren(l.reverse)
      }
      def addChildren(c: List[Element]): Element = {
        Element(children ++ toList)
      }
    }

This code is compatible with both Leon and Scala.
At parsing time, when Leon encounters a call to
`addChildren(a, b)`
using the first method, it translates it to
`addChildren(Cons(a, Cons(b, Nil())))`
using the second method.
When Scala encounters the same call,
it executes the `@ignore`-d function and calls the second method.

The reason is that the `scala.collection.Seq` used in the case of multiple arguments does not have a method `toList` that converts the sequence to a Leon `List`. Hence this workaround.

Compiling Leon programs to bytecode
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

If you don't use special constructs such as ``choose``, you should be able to
compile Leon programs to `.class` using `scalac` and execute them directly on
the JVM, or integrate them as part as other Scala-based projects.

Beware that you need to explicitly include files files from the Leon library
(that are implicitly bundled when you use the `./leon` script):

.. code-block:: bash

    $ mkdir out
    $ scalac $(find path/to/leon/library/ -name "*.scala" | xargs) MyFile.scala -d out
