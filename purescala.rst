.. _purescala:

Pure Scala
==========

The input to Leon is a purely functional **subset** of `Scala
<http://www.scala-lang.org/>`_, which we call 
**Pure Scala**. Constructs specific for Leon are defined inside
Leon's libraries in package `leon` and its subpackages. Leon
invokes standard `scalac` compiler on the input file, then
performs additional checks to ensure that the given program
belongs to Pure Scala.

Pure Scala supports two kinds of top-level declarations:

1. Algebraic Data Type (ADT) definitions in the form of an
   abstract class and case classes/objects

.. code-block:: scala

   abstract class MyList
   case object MyEmpty extends MyList
   case class MyCons(elem: BigInt, rest: MyList) extends MyList

2. Objects/modules, for grouping classes and functions

.. code-block:: scala

   object Specs {
      def increment(a: BigInt): BigInt = {
         a + 1
      }

      case class Identifier(id: BigInt)
   }

.. _adts:

Algebraic Data Types
--------------------

Abstract Classes
****************

ADT roots need to be defined as abstract, unless the ADT is defined with only one case class/object. Unlike in Scala, abstract classes cannot define fields or constructor arguments.

.. code-block:: scala

 abstract class MyType

An abstract class can be extended by other abstract classes.

Case Classes
************

The abstract root can also be extended by a case-class, defining several fields:

.. code-block:: scala

 case class MyCase1(f: Type, f2: MyType) extends MyType
 case class MyCase2(f: Int) extends MyType

.. note::
 You can also define single case-class, for Tuple-like structures.

Case Objects
************

It is also possible to defined case objects, without fields:

.. code-block:: scala

 case object BaseCase extends MyType


Generics
--------

Leon supports type parameters for classes and functions.

.. code-block:: scala

 object Test {
   abstract class List[T]
   case class Cons[T](hd: T, tl: List[T]) extends List[T]
   case class Nil[T]() extends List[T]

   def contains[T](l: List[T], el: T) = { ... }
 }


.. note::
 Type parameters are always **invariant**. It is not possible to define ADTs like:

 .. code-block:: scala

  abstract class List[T]
  case class Cons[T](hd: T, tl: List[T]) extends List[T]
  case object Nil extends List[Nothing]

 Leon in fact restricts type parameters to "simple hierarchies", where subclasses define the same type parameters in the same order.

Methods
-------

You can define methods in classes.

.. code-block:: scala

 abstract class List[T] {
   def contains(e: T) = { .. }
 }
 case class Cons[T](hd: T, tl: List[T]) extends List[T]
 case object Nil extends List[Nothing]

 def test(a: List[Int]) = a.contains(42)

It is possible to define abstract methods in abstract classes and implement them in case classes.
It is also possible to override methods.

.. code-block:: scala

  abstract class A {
    def x(a: Int): Int
  }

  abstract class B extends A {
    def x(a: Int) = {
      require(a > 0)
      42
    } ensuring { _ >= 0 }
  }

  case class C(c: Int) extends B {
    override def x(i: Int) = {
      require(i >= 0)
      if (i == 0) 0
      else c + x(i-1)
    } ensuring ( _ == c * i )
  }

  case class D() extends B

It is not possible, however, to call methods of a superclass with the ``super`` keyword.

Specifications
--------------

Leon supports three kinds of specifications to functions and methods:

Preconditions
*************

Preconditions constraint the argument and is expressed using `require`. It should hold for all calls to the function.

.. code-block:: scala

 def foo(a: Int, b: Int) = {
   require(a > b)
   ...
 }

Postconditions
**************

Postconditions constraint the resulting value, and is expressed using `ensuring`:

.. code-block:: scala

 def foo(a: Int): Int = {
   a + 1
 } ensuring { res => res > a }

Body Assertsions
****************

Assertions constrain intermediate expressions within the body of a function.

.. code-block:: scala

 def foo(a: Int): Int = {
   val b = -a
   assert(a >= 0 || b >= 0, "This will fail for -2^31")
   a + 1
 }

The error description (last argument of ``assert``) is optional.

Expressions
-----------

Leon supports most purely-functional Scala expressions:

Pattern matching
****************

.. code-block:: scala

 expr match {
   // Simple (nested) patterns:
   case CaseClass( .. , .. , ..) => ...
   case v @ CaseClass( .. , .. , ..) => ...
   case v : CaseClass => ...
   case (t1, t2) => ...
   case 42 => ...
   case _ => ...

   // can also be guarded, e.g.
   case CaseClass(a, b, c) if a > b => ...
 }

Custom pattern matching with ``unapply`` methods are also supported:

.. code-block:: scala

 object :: {
   def unapply[A](l: List[A]): Option[(A, List[A])] = l match {
     case Nil() => None()
     case Cons(x, xs) => Some((x, xs))
   }
 }
  
 def empty[A](l: List[A]) = l match {
   case x :: xs => false
   case Nil() => true
 }

Values
******

.. code-block:: scala

 val x = ...

 val (x, y) = ...

 val Cons(h, _) = ...

.. note::
 The latter two cases are actually syntactic sugar for pattern matching with one case.


Inner Functions
***************

.. code-block:: scala

 def foo(x: Int) = {
   val y = x + 1
   def bar(z: Int) = {
      z + y
   }
   bar(42)
 }


Predefined Types
****************

TupleX
######

.. code-block:: scala

 val x = (1,2,3)
 val y = 1 -> 2 // alternative Scala syntax for Tuple2
 x._1 // == 1

Boolean
#######

.. code-block:: scala

  a && b
  a || b
  a == b
  !a
  a ==> b // Leon syntax for boolean implication

Int
###

.. code-block:: scala

 a + b
 a - b
 -a
 a * b
 a / b
 a % b // a modulo b
 a < b
 a <= b
 a > b
 a >= b
 a == b

.. note::
 Integers are treated as 32bits integers and are subject to overflows.

BigInt
######

.. code-block:: scala

 val a = BigInt(2)
 val b = BigInt(3)

 -a
 a + b
 a - b
 a * b
 a / b
 a % b // a modulo b
 a < b
 a > b
 a <= b
 a >= b
 a == b

.. note::
 BigInt are mathematical integers (arbitrary size, no overflows).

Real
####

``Real`` represents the mathematical real numbers (different from floating points). It is an
extension to Scala which is meant to write programs closer to their true semantics.

.. code-block:: scala

 val a: Real = Real(2)
 val b: Real = Real(3, 5) // 3/5

 -a
 a + b
 a - b
 a * b
 a / b
 a < b
 a > b
 a <= b
 a >= b
 a == b

.. note::
  Real have infinite precision, which means their properties differ from ``Double``.
  For example, the following holds:

  .. code-block:: scala

    def associativity(x: Real, y: Real, z: Real): Boolean = {
      (x + y) + z == x + (y + z)
    } holds

  While it does not hold with floating point arithmetic.


Set
###

.. code-block:: scala

 import leon.lang.Set // Required to have support for Sets

 val s1 = Set(1,2,3,1)
 val s2 = Set[Int]()

 s1 ++ s2 // Set union
 s1 & s2  // Set intersection
 s1 -- s2 // Set difference
 s1 subsetOf s2
 s1 contains 42


Functional Array
################

.. code-block:: scala

 val a = Array(1,2,3)

 a(index)
 a.updated(index, value)
 a.length


Map
###

.. code-block:: scala

 import leon.lang.Map // Required to have support for Maps

 val  m = Map[Int, Boolean](42 -> false)

 m(index)
 m isDefinedAt index
 m contains index
 m.updated(index, value)
 m + (index -> value)
 m + (value, index)
 m.get(index)
 m.getOrElse(index, value2)


Function
########

.. code-block:: scala

 val f1 = (x: Int) => x + 1                 // simple anonymous function

 val y  = 2
 val f2 = (x: Int) => f1(x) + y             // closes over `f1` and `y`
 val f3 = (x: Int) => if (x < 0) f1 else f2 // anonymous function returning another function

 list.map(f1)      // functions can be passed around ...
 list.map(f3(1) _) // ... and partially applied

.. note::
 No operators are defined on function-typed expressions, so specification is
 currently quite limited.


Symbolic Input-Output examples
------------------------------

Sometimes, a complete formal specification is hard to write,
especially when it comes to simple, elementary functions. In such cases,
it may be easier to provide a set of IO-examples. On the other hand,
IO-examples can never cover all the possible executions of a function,
and are thus weaker than a formal specification. 

Leon provides a powerful compromise between these two extremes.
It introduces *symbolic IO-examples*, expressed through a specialized ``passes``
construct, which resembles pattern-matching:

.. code-block:: scala

  sealed abstract class List {
    
    def size: Int = (this match {
      case Nil() => 0
      case Cons(h, t) => 1 + t.size
    }) ensuring { res => (this, res) passes {
      case Nil() => 0
      case Cons(_, Nil()) => 1
      case Cons(_, Cons(_, Nil())) => 2
    }}
  }
  case class Cons[T](h: T, t: List[T]) extends List[T]
  case class Nil[T]() extends List[T]


In the above example, the programmer has chosen to partially specify ``size``
through a list of IO-examples, describing what the function should do 
for lists of size 0, 1 or 2.
Notice that the examples are symbolic, in that the elements of the lists are
left unconstrained.

The semantics of ``passes`` is the following.
Let ``a: A`` be a tuple of method parameters and/or ``this``, ``b: B``,
and for each i ``pi: A`` and ``ei: B``. Then

.. code-block:: scala

  (a, b) passes {
    case p1 => e1
    case p2 => e2
    ...
    case pN => eN
  }

is equivalent to

.. code-block:: scala

  a match {
    case p1 => b == e1
    case p2 => b == e2
    ...
    case pN => b == eN
    case _  => true
  }
