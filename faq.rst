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
