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

You can add invariants to case classes using a ``require`` clause, as follows:

.. code-block:: scala

  case class Positive(value: BigInt = 0) {
    require(value >= 0)
  }

For classes without type parameters, when all fields have a default value, Stainless generates a
verification condition to check that the default instance respects the invariant. In this example,
the verification condition will be seen as coming from an internal function called
``PositiveRequireForDefault``.

.. note::

  Invariants are only allowed to refer to fields of their class, and
  cannot call any methods on ``this`` (but calls to methods on their
  fields are allowed).

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

   Same remark as above: invariants are only allowed to refer to fields of their class.

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

Abstract methods may have contracts in terms of pre- and postconditions. The
syntax uses ``???`` and is as follows:

.. code-block:: scala

  abstract class Set[T] {
    def contains[T](t: T): Boolean

    def add[T](t: T): Set[T] = {
      require(!this.contains(t))
      (??? : Set[T])
    }.ensuring(res => res.contains(t))
  }

You can then extend such abstract classes by concrete implementations, and
Stainless will generate verification conditions to make sure that the
implementation respects the specification.

You can also add implementations and assume that they are correct with respect
to the specification of the abstract class, without having Stainless check the
specification (e.g. if you want to use existing Scala data-structures inside).
In that case, mark the concrete class with ``@extern`` (see Section :doc:`wrap`
for more info on ``@extern``) or place the concrete implementation in files
which are not inspected by Stainless (see e.g.
https://github.com/epfl-lara/stainless-project.g8 for an example of how to setup
such a hybrid project).


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


Initialization
**************

In Pure Scala, initialization of ``val``'s  may not have future or self-references:

.. code-block:: scala

  object Initialization {
    case class C(x: BigInt) {
      val y = x       // ok
      val z = y + x   // ok
      val a = b       // Error: "because field `a` can only refer to previous fields, not to `b`"
      val b = z + y   // ok
    }
  }


Overriding
**********

Stainless supports overriding methods with some constraints:
* A ``val`` in an abstract class can only be overridden by a concrete class parameter.
* Methods and ``lazy val``s in abstract classes can be overridden by concrete methods or
``lazy val``'s (interchangably), or by a concrete class parameter, but not by
a ``val``.

Here are a few examples that are rejected by Stainless:

.. code-block:: scala

  object BadOverride1 {
    sealed abstract class Abs {
      require(x != 0)
      val x: Int
    }

    // Error: "Abstract values `x` must be overridden with fields in concrete subclass"
    case class AbsInvalid() extends Abs {
      def x: Int = 1
    }
  }

.. code-block:: scala

  object BadOverride2 {
    sealed abstract class Abs {
      val y: Int
    }

    // Error: "Abstract values `y` must be overridden with fields in concrete subclass"
    case class AbsInvalid() extends Abs {
      val y: Int = 2
    }
  }

.. code-block:: scala

  object BadOverride3 {
    sealed abstract class AAA {
      def f: BigInt
    }

    // Error: "because abstract methods BadOverride3.AAA.f were not overridden by
    //         a method, a lazy val, or a constructor parameter"
    case class BBB() extends AAA {
      val f: BigInt = 0
    }
  }


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
abstract within an abstract class and overridden in implementations:

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



Bitvectors
**********

Bitvectors are currently only supported in GenC and for verification, but
`not for compilation <https://github.com/epfl-lara/stainless/issues/982>`_.

These examples are taken from `BitVectors3.scala
<https://github.com/epfl-lara/stainless/blob/master/frontends/benchmarks/verification/valid/MicroTests/BitVectors3.scala>`_.

.. code-block:: scala

  import stainless.math.BitVectors._

  val x1: UInt8 = 145
  val x2: Int8 = x1.toSigned[Int8] // conversion from unsigned to signed ints

  // Bitvectors can be compared to literal constants, which are encoded as a bitvector of the same
  // type as the left-hand-side bitvector.
  // In the line below, `-111` get encoded internally as an `Int8`.
  assert(x2 == -111)

  // In Stainless internals, `Int8` and `Byte` are the same type, but not for the surface language,
  // so `toByte` allows to go from `Int8` to `Byte`.
  // Similarly, we support `toShort`, `toInt`, `toLong` for conversions
  // respectively from `Int16` to `Short`, `Int32` to `Int`, `Int64` to `Long`,
  // and `fromByte`, `fromShort`, `fromInt`, `fromLong` for the other direction
  val x3: Byte = x2.toByte
  assert(x3 == -111)

  // Unsigned ints can be cast to larger unsigned types
  val x4: UInt12 = x1.widen[UInt12]
  assert(x4 == 145)

  // or truncated to smaller unsigned types.
  val x5: UInt4 = x1.narrow[UInt4]
  assert(x5 == 1) // 145 % 2^4 == 1

  // Signed ints can also be cast to larger signed types (using sign extension)
  val x6: Int8 = 120
  val x7: Int12 = x6.widen[Int12]
  assert(x7 == 120)

  // and cast to smaller signed types.
  // This corresponds to extracting the least significant bits of the representation
  // (see `extract` here http://smtlib.cs.uiowa.edu/logics-all.shtml).
  val x8: Int4 = x6.narrow[Int4]
  assert(x8 == -8)

  // the `toByte`, `toShort`, `toInt`, and `toLong` methods described above
  // can be used on any bitvector type. For signed integers, this corresponds
  // to a narrowing or a widening operation depending on the bitvector size.
  // For unsigned integers, this corresponds to first doing a widening/narrowing
  // operation, and then applying `toSigned`
  val x9: UInt2 = 3
  assert(x9.toInt == x9.widen[UInt32].toSigned[Int32].toInt)

  // The library also provide constants for maximum and minimum values.
  assert(max[Int8] == 127)
  assert(min[Int8] == -128)


Arrays, which are usually indexed using ``Int``, may also be indexed using the bitvector types.
This is similar to first converting the bitvector index using ``toInt``.

Bitvector types can be understood as finite intervals of integers
(two's complement representation). For ``X`` an integer larger than ``1``
(and at most ``256`` in Stainless):

* ``UIntX`` is the interval :math:`[0, 2^X - 1]`,
* ``IntX`` is the interval :math:`[-2^{X-1}, 2^{X-1} - 1]`.

Conversions between these types can be interpreted as operations on the
arrays of bits of the bitvectors, or as operations on the integers they
represent.

* ``widen`` from ``UIntX`` to ``UIntY`` with :math:`Y > X` adds :math:`Y-X` (most significant) 0-bits, and corresponds to the identity transformation on integers.

* ``widen`` from ``IntX`` to ``IntY`` with :math:`Y > X` copies :math:`Y-X` times the sign bit (sign-extension), and corresponds to the identity transformation on integers.

* ``narrow`` from ``UIntX`` to ``UIntY`` with :math:`Y < X` removes the :math:`X-Y` most significant bits,
  and corresponds to taking the number modulo :math:`2^Y`.
  When the ``strict-arithmetic`` option is enabled, narrowing a number ``n`` to ``UIntY`` generates
  a check ``n < 2^Y``.

* ``narrow`` from ``IntX`` to ``IntY`` with :math:`Y < X` removes the :math:`X-Y` most significant bits (including the sign bit),
  and corresponds to the identity for integers in the interval :math:`[-2^{Y-1}, 2^{Y-1} - 1]`. Outside this range,
  the narrowing operation on a number ``n`` can be described as: 1) (unsigning) adding ``2^X`` if ``n`` is negative,
  2) (unsigned narrowing) taking the result modulo ``2^Y``, 3) (signing) removing ``2^Y`` if the result of (2) is
  greater or equal than ``2^{Y-1}``.
  In ``strict-arithmetic`` mode, narrowing a number ``n`` to ``IntY`` generates two checks: ``-2^{Y-1} <= n`` and ``n <= 2^{Y-1} - 1``.

* ``toSigned`` from ``UIntX`` to ``IntX`` does not change the bitvector, and behaves as the identity for integers not larger than :math:`2^{X-1}-1`,
  and subtracts :math:`2^{X}` for integers in the interval :math:`[2^{X-1}, 2^{X} - 1]`.
  In ``strict-arithmetic`` mode, making a number ``n`` signed generates a check ``n <= 2^{X-1}-1``.

* ``toUnsigned`` from ``IntX`` to ``UIntX`` does not change the bitvector, and behaves as the identity
  for non-negative integers, and adds :math:`2^{X}` for negative integers (in the interval :math:`[-2^{X-1}, 0[`).
  In ``strict-arithmetic`` mode, making a number ``n`` unsigned generates a check ``n >= 0``.
