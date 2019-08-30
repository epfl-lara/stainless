.. _laws:

Specifying Algebraic Properties
===============================

Introduction
------------

Many datatypes that programmers deal with on a day-to-day basis often provide
the same set of operations, for example:

- They can be tested for equality to some other value
- They can be ordered (partially or totally)
- They can be composed together
- They can be added or multiplied together
- They have an inverse with respect to some operation

Because those are very common properties, it is often useful to be able to
abstract over them. In fact, each of these properties corresponds to an
algebraic structure, and is governed by the set of laws which allow the
programmer to reason at a higher level of abstraction, and to be able
to rely on the behavior specified by the laws associated with the structure.

While these properties can be modeled and implemented using Java interfaces,
modern programming languages such as Scala or Haskell provide a better
mechanism for expressing the properties: typeclasses.

Typeclasses
-----------

Typeclasses were introduced by Wadler & Blott [WB89]_ as an extension
to the Hindley/Milner type system to implement a certain kind of overloading,
known as *ad-hoc* polymorphism.

A typeclass is identified by its name, and is associated with a set of
(usually polymorphic) functions signatures, its *methods*.

It can then be *instantiated* at various types, given that the user is able
to provide a concrete implementation for each method. A user can then apply
these methods to any type for which there is a corresponding instance, which
essentially corresponds to *overloading*.

Using typeclasses, one can model algebraic properties of datatypes in a fairly natural way.
Here is for example, the definition and implementation of a ``Monoid``, ie. a typeclass
for datatypes which can be mashed together associatively, and which have an
identity element w.r.t. to this operation:

.. code-block:: scala

  abstract class Monoid[A] {
    def empty: A
    def append(x: A, y: A): A

    @law
    def law_leftIdentity(x: A) = {
      append(empty, x) == x
    }

    @law
    def law_rightIdentity(x: A) = {
      append(x, empty) == x
    }

    @law
    def law_associativity(x: A, y: A, z: A) = {
      append(x, append(y, z)) == append(append(x, y), z)
    }
  }

  implicit val bigIntAdditiveMonoid: Monoid[BigInt] = new Monoid[BigInt] {
    override def empty: BigInt = 0
    override def append(x: BigInt, y: BigInt): BigInt = x + y
  }

Here, the abstract class specifies the two abstract operations which are required,
but also the associated laws that the implementation of these operations must
satisfy for the datatype to form a valid monoid.

Stainless will then ensure that the implementation of ``Monoid`` for the ``BigInt`` type satisfy
those laws. In this case, the above definition of ``bigIntAdditiveMonoid`` will generate the
following verification conditions:::

     ┌───────────────────┐
   ╔═╡ stainless summary ╞══════════════════════════════════════════════════════════════════════╗
   ║ └───────────────────┘                                                                      ║
   ║ law_associativity     law              valid   nativez3   ../../test.scala:25:3     0.052  ║
   ║ law_leftIdentity      law              valid   nativez3   ../../test.scala:25:3     0.037  ║
   ║ law_rightIdentity     law              valid   nativez3   ../../test.scala:25:3     0.029  ║
   ╟--------------------------------------------------------------------------------------------╢
   ║ total: 9    valid: 9    (0 from cache) invalid: 0    unknown: 0    time:   0.729           ║
   ╚════════════════════════════════════════════════════════════════════════════════════════════╝

Armed with the knowledge that our ``Monoid`` will always be lawful, one can now fearlessly write
the ``foldMap`` function, and get the expected result:

.. code-block:: scala

  def foldMap[A, M](xs: List[A])(f: A => M)(implicit M: Monoid[M]): M = xs match {
    case Nil() => M.empty
    case Cons(y, ys) => M.append(f(y), foldMap(ys)(f))
  }

  def sumBigInt(xs: List[BigInt]): BigInt = {
    foldMap(xs)(x => x)
  }

Sometimes, Stainless will not be able to automatically prove that an instance is lawful,
for example when the property of interest involves a recursive definition over an inductive
data type, as in the following code:

.. code-block:: scala

  sealed abstract class Nat {
    def +(m: Nat): Nat = this match {
      case Zero => m
      case Succ(n) => Succ(n + m)
    }

    def *(m: Nat): Nat = this match {
      case Zero => Zero
      case Succ(n) => n * m + m
    }
  }

  final case object Zero extends Nat
  final case class Succ(prev: Nat) extends Nat

  final val One = Succ(Zero)

  implicit def natAdditiveMonoid: Monoid[Nat] = new Monoid[Nat] {
    def empty: nat = Zero
    def append(x: Nat, y: Nat): Nat = x + y
  }

To help Stainless out, one needs to prove that ``Zero`` indeed the right identity of ``+``,
as well as the associativity of the latter.

.. code-block:: scala

  @induct
  def lemma_rightIdentity_plus(x: Nat): Boolean = {
    x + Zero == x
  }.holds

  @induct
  def lemma_associativity_plus(x: Nat, y: Nat, z: Nat): Boolean = {
    x + (y + z) == (x + y) + z
  }.holds

One can then override the law of interest, and instantiate the lemma over the relevant parameters:

.. code-block:: scala

  implicit def natAdditiveMonoid: Monoid[Nat] = new Monoid[Nat] {
    def empty: nat = Zero
    def append(x: Nat, y: Nat): Nat = x + y

    override def law_rightIdentity(x: Nat) = {
      super.law_rightIdentity(x) because lemma_rightIdentity_plus(x)
    }

    override def law_associativity(x: Nat, y: Nat, z: Nat) = {
      super.law_associativity(x, y, z) because lemma_associativity_plus(x, y, z)
    }
  }

With these modifications, the example goes through without a hitch.

Typeclass inheritance
---------------------

Some algebraic structures can be defined as some other algebraic structure plus some additional
operations and/or laws, eg. a monoid can be seen as a semigroup with identity.

In Scala, typeclasses allow to represent such relationship between algebraic structures by mean of inheritance.

Let's take for example the ``Ord`` typeclass, which describes totally ordered datatypes.

This class is defined as follows:

.. code-block:: scala

  trait Eq[A] {
    def equals(x: A, y: A): Boolean
  }

  trait Ord[A] extends Eq[A] {
    def lessThanEq(x: A, y: A): Boolean

    def lessThan(x: A, y: A): Boolean = lessThanEq(x, y) && !equals(x, y)
  }

This can also be read as: if ``A`` is an instance of ``Ord``, then it also is a instance of ``Eq``.

Associated methods
------------------

On top of abstract operations, a typeclass can also introduces concrete methods which
do not need to (but can) be re-defined by the programmer at instance declaration time,
just like the ``lessThan`` method of the ``Ord`` class above.

While such methods could be defined as a standalone function with an ``Ord`` constraint,
having it be a part of the class allows users to override it with e.g. a more efficient
implementation specific to the datatype they are instantiating the class for, as shown below:

.. code-block:: scala

  case object BigIntOrd extends Ord[BigInt] {
    def equal(x: BigInt, y: BigInt) = x == y
    def lessThanEq(x: BigInt, y: BigInt) = x <= y

    override def lessThan(x: BigInt, y: BigInt) x < y
  }

Coherence
---------

Let's now look at an issue that might arise when working with typeclasses in Scala.

.. code-block:: scala

  abstract class Monoid[A] {
    def empty: A
    def combine(x: A, y: A): A
  }

  implicit val bigIntAddMonoid: Monoid[BigInt] = new Monoid[BigInt] {
    override def empty: BigInt = 0
    override def combine(x: BigInt, y: BigInt): BigInt = x + y
  }

  implicit val bigIntProdMonoid: Monoid[BigInt] = new Monoid[BigInt] {
    override def empty: BigInt = 1
    override def combine(x: BigInt, y: BigInt): BigInt = x * y
  }

  def fold[A](list: List[A])(implicit M: Monoid[A]): A = {
    list.foldRight(M.empty)(M.combine)
  }

  val list: List[BigInt] = List(2, 3)
  val res: BigInt = fold(list) // ?

Here, the Scala compiler bails out with an *ambiguous implicits* error but for good reasons this time.
Indeed, depending on which instance of ``Monoid[BigInt]`` it picks, ``res`` can either be equal to 5 or 6.
This issue arise because the two instances above are *overlapping*, which has the effect of making the
type system *incoherent*.  For a type system to be coherent, "every valid typing derivation for a program
must lead to a resulting program that has the same dynamic semantics", which is clearly not the case here.
While in this specific example, the compiler will rightfully reject the program, this might always be
possible as one could import a different instance in scope in two different modules, and then a third module
might assume that these modules actually make use of the same instance, silently breaking the program.
Imagine trying to merge two ``Sets`` that have been created with two different ``Ord`` instances in scope.

Haskell partially solves this problem by enforcing that instances defined in the same module do not overlap,
that is to say that the compiler would reject the program above. We deem Haskell's approach only partial as
it allows the programmer to define two or more overlapping instances, provided that they are not defined in the same module.
A program is then only rejected when the programmer makes imports such overlapping instances in scope and
attempts to make use of them. This decision stems from the will to allow linking together two different
libraries which both define a class instance for the same type.

Because Stainless operates under a closed-world assumption, we could go further and disallow overlapping
instances altogether, but this has not been implemented yet.

One might still want to provide both an additive and multiplicative ``Monoid`` instance for integers.
To this end, one can wrap values of type ``BigInt`` with two different wrapper classes for which
we will define the respective instances:

.. code-block:: scala

  case class Sum(value: BigInt)     extends AnyVal
  case class Product(value: BigInt) extends AnyVal

  implicit val bigIntSumMonoid: Monoid[Sum] = new Monoid[Sum] {
    override def empty: Sum = Sum(0)
    override def combine(x: Int, y: Int): Sum = Sum(x.value + y.value)
  }

  implicit val bigIntProductMonoid: Monoid[Product] = new Monoid[Product] {
    override def empty: Product = Product(1)
    override def combine(x: Int, y: Int): Product = Product(x.value * y.value)
  }

.. code-block:: scala

  def foldMap[A, B](list: List[A])(f: A => B)(implicit M: Monoid[B]): B = {
    list.map(f).foldRight(M.empty)(M.combine)
  }

It then becomes possible to unambiguously pick which instance to use depending on the semantics one wants:

.. code-block:: scala

  val list: List[BigInt] = List(2, 3)

  val sum: BigInt     = foldMap(list)(Sum(_)).value     // 5
  val product: BigInt = foldMap(list)(Product(_)).value // 6

Under the hood
--------------

In this section we describe how laws are encoded. Let's take as an example the
following typeclass:

.. code-block:: scala

  abstract class Structure[A] {
    def doSomething(x: A, y: A): A

    @law
    def someLaw(x: A, y: A): Boolean = {
      doSomething(x, y) == doSomething(y, x)
    }
  }



And a valid instance for ``BigInt``:

.. code-block:: scala

  val bigIntInstance: Structure[BigInt] = new Structure[BigInt] {
    override def doSomething(x: BigInt, y: BigInt): BigInt = {
      x + y
    }

    override def someLaw(x: BigInt, y: BigInt): Boolean = {
      super.someLaw(x, y) because {
        x + y == y + y
      }
    }
  }



.. code-block:: scala

  abstract class Structure[A] {
    @abstract
    def doSomething(x: A, y: A): Boolean = {
      <empty tree>[A]
    }

    @abstract
    def someLaw(x: A, y: A): Boolean = {
      <empty tree>[Boolean]
    } ensuring { res => res && this.someLawProp(x, y) }

    def someLawProp(x: A, y: A): Boolean = {
      this.doSomething(x, y) == this.doSomething(y, x)
    }
  }

  val bigIntInstance: Structure[BigInt] = new Structure[BigInt] {
    def doSomething(x: BigInt, y: BigInt): BigInt = {
      x + y
    }

    def someLaw(x: BigInt, y: BigInt): Boolean = {
      super.someLaw(x, y) because {
        x + y == y + x
      }
    }
  }

.. code-block:: scala

  abstract class A {
    def x: BigInt

    @law def constraint = x != 0
  }

  abstract class B extends A

  abstract class C extends B {
    override def constraint = x > 0
  }

  case class D() extends C {
    def x = 42
  }

.. code-block:: scala

  abstract class A {
    def x: BigInt

    @law def constraint$1 = {
      <empty tree>[Boolean]
    } ensuring { res => res && this.constraintProp$1 }

    def constraintProp$1 = x != 0
  }

  abstract class B extends A {
    @law def constraint$2 = {
      super.constraint$1 && this.constraintProp$2
    }

    def constraintProp$2 = true
  }

  abstract class C extends B {
    @law def constraint$3 = {
      super.constraint$2 && this.constraintProp$3
    }

    def constraintProp$3 = x > 0
  }

  case class D() extends C {
    def x = 42

    @law def constraint$3 = {
      super.constraint$3 && this.constraintProp$4
    }

    def constraintProp$4 = true
  }

.. note::

  As can be seen above, calling the super method when refining or proving a law is superfluous,
  since it is done anyway during the encoding, but can help readability, as doing so makes the
  code more closely match the semantics of Stainless.

.. [WB89] P. Wadler and S. Blott. 1989. How to make ad-hoc polymorphism less ad hoc.
