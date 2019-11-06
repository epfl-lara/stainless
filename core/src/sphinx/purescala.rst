.. _purescala:

Pure Scala
==========

The input to Stainless is a purely functional **subset** of `Scala
<http://www.scala-lang.org/>`_, which we call
**Pure Scala**. Constructs specific for Stainless are defined inside
Stainless's libraries in package `stainless` and its subpackages.
Stainless invokes standard `scalac` compiler on the input file, then
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

Booleans
--------

Booleans are used to express truth conditions in Stainless.
Unlike some proof assistants, there is no separation
at the type level between
Boolean values and the truth conditions of conjectures
and theorems.

Typical propositional operations are available using Scala
notation, along
with a new shorthand for implication. The `if` expression
is also present.

.. code-block:: scala

  a && b
  a || b
  a == b
  !a
  a ==> b // Stainless syntax for boolean implication

Stainless uses short-circuit interpretation of `&&`, `||`, and `==>`,
which evaluates the second argument only when needed:

.. code-block:: scala

  a && b  === if (a) b else false

  a || b  === if (a) true else b

  a ==> b === if (a) b else true

This aspect is important because of:

1. evaluation of expressions, which is kept compatible with Scala

2. verification condition generation for safety: arguments of Boolean operations
may be operations with preconditions; these preconditions apply only in case
that the corresponding argument is evaluated.

3. termination checking, which takes into account that only one of the paths in an if expression is evaluated for a given truth value of the condition.

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

Value Classes
*************

One can define a value class just like in standard Scala,
by extending the ``AnyVal`` class.

.. code-block:: scala

  case class Positive(value: BigInt) extends AnyVal {
    @invariant
    def isPositive: Boolean = value >= 0
  }

In the code block above, we also specify an invariant of the value
class, using the ``@invariant`` annotation. Such invariants are
subsequently lifted into a refinement type of the underlying type.

.. note::

   Invariants are only allowed to refer to fields of their class, and
   cannot call any methods on ``this`` (but calls to methods on their
   fields are allowed).

Generics
--------

Stainless supports type parameters for classes and functions.

.. code-block:: scala

  object Test {
    abstract class List[T]
    case class Cons[T](hd: T, tl: List[T]) extends List[T]
    case class Nil[T]() extends List[T]

    def contains[T](l: List[T], el: T) = { ... }
  }


.. note::
  Type parameters can also be marked as co- or contra-variant, eg.

  .. code-block:: scala

    abstract class List[+T]
    case class Cons[T](hd: T, tl: List[T]) extends List[T]
    case object Nil extends List[Nothing]

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
Multiple layers of inheritance are allowed, as is the ability to override concrete methods.

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

It is also possible to call methods of a superclass with the ``super`` keyword.

.. code-block:: scala

  sealed abstract class Base {
    def double(x: BigInt): BigInt = x * 2
  }

  case class Override() extends Base {
    override def double(x: BigInt): BigInt = {
      super.double(x + 1) + 42
    }
  }

Copy Method
***********

The ``copy`` method of classes with immutable fields is extracted as well,
and ensures that the class invariant (if any) is maintained by requiring it
to be satisfied as a precondition.

.. code-block:: scala

  case class Foo(x: BigInt) {
    require(x > 0)
  }

  def prop(foo: Foo, y: BigInt) = {
    require(y > 1)
    foo.copy(x = y)
  }

.. note::
  The example above would not verify without the precondition in function ``prop``,
  as ``Foo`` require its field ``x`` to be positive.


Default Parameters
******************

Functions and methods can have default values for their parameters.

.. code-block:: scala

  def test(x: Int = 21): Int = x * 2

  assert(test() == 42) // valid


Type Definitions
----------------

Type Aliases
************

Type aliases can be defined the usual way:

.. code-block:: scala

   object testcase {
     type Identifier = String

     def newIdentifier: Identifier = /* returns a String */
   }

Type aliases can also have one or more type parameters:

.. code-block:: scala

   type Collection[A] = List[A]

   def singleton[A](x: A): Collection[A] = List(x)

Type Members
************

Much like classes can have field members and method members, they can also
define type members. Much like other members, those can also be declared
abstract within an abstract class and overriden in implementations:

.. code-block:: scala

  case class Grass()

  abstract class Animal {
    type Food
    val happy: Boolean
    def eat(food: Food): Animal
  }

  case class Cow(happy: Boolean) extends Animal {
    type Food = Grass
    def eat(g: Grass): Cow = Cow(happy = true)
  }

Note: Like regular type aliases, type members can also have one or more type parameters.

Type members then give rise to path-dependent types, where the type of a variable
can depend on another variable, by selecting a type member on the latter:

.. code-block:: scala

  //                             Path-dependent type
  //                                 vvvvvvvvvvv
  def giveFood(animal: Animal)(food: animal.Food): Animal = {
    animal.eat(food)
  }

  def test = {
    val cow1 = Cow(false)
    val cow2 = giveFood(cow1)(Grass())
    assert(cow2.happy) // VALID
  }

Specifications
--------------

Stainless supports three kinds of specifications to functions and methods:

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

Body Assertions
***************

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

Stainless supports most purely-functional Scala expressions:

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


Local and Anonymous Classes
***************************

Functions and methods can declare local classes, which can close over
the fields of the enclosing class, as well as the parameters of the enclosing
function or method.

.. code-block:: scala

  abstract class Foo {
    def bar: Int
  }

  def makeFoo(x: Int): Foo = {
    case class Local() extends Foo {
      def bar: Int = x
    }
    Local()
  }

.. note:: Functions and methods which return an instance of a local class
          must have an explicit return type, which will typically be that of the parent class.
          Otherwise, a structural type will be inferred by the Scala compiler, and those are
          currently unsupported.

Anonymous classes with an explicit parent are supported as well:

.. code-block:: scala

  abstract class Foo {
    def bar: Int
  }

  def makeFoo(x: Int): Foo = new Foo {
    def bar: Int = x
  }

.. note:: Anonymous classes cannot declare more public members than their parent class,
          ie. the following is not supported:

.. code-block:: scala

  abstract class Foo {
    def bar: Int
  }

  def makeFoo(x: Int): Foo = new Foo {
    def bar: Int = x
    def hi: String = "Hello, world"
  }

Predefined Types
----------------

TupleX
******

.. code-block:: scala

  val x = (1,2,3)
  val y = 1 -> 2 // alternative Scala syntax for Tuple2
  x._1 // == 1


Int
***

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
******

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
****

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
***

.. code-block:: scala

  import stainless.lang.Set // Required to have support for Sets

  val s1 = Set(1,2,3,1)
  val s2 = Set[Int]()

  s1 ++ s2 // Set union
  s1 & s2  // Set intersection
  s1 -- s2 // Set difference
  s1 subsetOf s2
  s1 contains 42


Functional Array
****************

.. code-block:: scala

  val a = Array(1,2,3)

  a(index)
  a.updated(index, value)
  a.length


Map
***

.. code-block:: scala

  import stainless.lang.Map // Required to have support for Maps

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
********

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


