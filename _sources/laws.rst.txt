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
following verification conditions::

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

In this section we describe how laws are encoded within Stainless.

Let's take as an example the Semigroup+Monoid hierarchy, slightly
amended to exercise at once all the features described above.

.. code-block:: scala

   abstract class Semigroup[A] {
     def append(x: A, y: A): A

     @law
     def law_associativity(x: A, y: A, z: A): Boolean = {
       append(x, append(y, z)) == append(append(x, y), z)
     }
   }

   abstract class Monoid[A] extends Semigroup[A] {
     def empty: A

     @law
     def law_leftIdentity(x: A): Boolean = {
       append(empty, x) == x
     }

     @law
     def law_rightIdentity(x: A): Boolean = {
       append(x, empty) == x
     }

     override def law_associativity(x: A, y: A, z: A): Boolean = {
       // We refine the Semigroup associativity law with a dummy
       // predicate `refineLaw` to demonstrate this feature.
       super.law_associativity(x, y, z) && refineLaw(x, y, z)
     }
   }

   def refineLaw[A](x: A, y: A, z: A): Boolean = true

Together with a simple implementation for ``BigInt``:

.. code-block:: scala

  def bigIntAdditiveMonoid: Monoid[BigInt] = new Monoid[BigInt] {
    def empty: BigInt = 0
    def append(x: BigInt, y: BigInt): BigInt = x + y

    override def law_rightIdentity(x: BigInt): Boolean = {
      // no manual proof is needed in this case, but we include
      // a dummy one for the sake of this example.
      someProof
    }
  }

  def someProof: Boolean = true

Here is the internal Stainless AST pretty much right after extraction
from the Scala compiler.

Each symbol (class, method, variable) is annotated with its internal identifier
(ie. the number after the ``$`` sign at the end of its name) which will prove useful
for reading the code after the next phase, as it introduces new symbols with the same
name but different identifiers.

.. code-block:: scala

   abstract class Semigroup$0[A$85] {

     @abstract
     def append$3(x$108: A$85, y$24: A$85): A$85 = <empty tree>[A$85]

     @law
     def law_associativity$0(x$109: A$85, y$25: A$85, z$11: A$85): Boolean = {
       this.append$3(x$109, this.append$3(y$25, z$11)) ==
       this.append$3(this.append$3(x$109, y$25), z$11)
      }
   }

   abstract class Monoid$0[A$86] extends Semigroup$0[A$86] {

     @abstract
     def empty$6: A$86 = <empty tree>[A$86]

     @law
     def law_leftIdentity$0(x$110: A$86): Boolean =
      this.append$3(this.empty$6, x$110) == x$110

     @law
     def law_rightIdentity$0(x$111: A$86): Boolean =
      this.append$3(x$111, this.empty$6) == x$111

     def law_associativity$1(x$112: A$86, y$26: A$86, z$12: A$86): Boolean =
       super.law_associativity$0(x$112, y$26, z$12) && refineLaw$0[A$86](x$112, y$26, z$12)
   }

   def refineLaw$0[A$87](x$113: A$87, y$27: A$87, z$13: A$87): Boolean = true

   case class $anon$0() extends Monoid$0[BigInt] {
     def empty$7: BigInt = 0
     def append$4(x$112: BigInt, y$26: BigInt): BigInt = x$112 + y$26

     def law_rightIdentity$1(x$113: BigInt): Boolean = someProof$0
   }

   def bigIntAdditiveMonoid$0: Monoid$0[BigInt] = $anon$0()

   def someProof$0: Boolean = true

The code above maps in straightforward way to the original code.

Let's now take a look at the output of the ``Laws`` phase. This is
the phase which desugars the law definitions and their overrides
into methods with explicit postconditions.

.. code-block:: scala

   abstract class Semigroup$0[A$85] {

     @abstract
     def append$3(x$108: A$85, y$24: A$85): A$85 = <empty tree>[A$85]

     @final
     @inlineOnce
     @derived(law_associativity$0)
     def law_associativity$2(x$120: A$85, y$30: A$85, z$14: A$85): Boolean = {
       this.append$3(x$120, this.append$3(y$30, z$14)) ==
       this.append$3(this.append$3(x$120, y$30), z$14)
     }

     @abstract
     def law_associativity$0(x$109: A$85, y$25: A$85, z$11: A$85): Boolean = {
       <empty tree>[Boolean]
     } ensuring {
       (res$82: Boolean) => res$82 && this.law_associativity$2(x$109, y$25, z$11)
     }
   }

   abstract class Monoid$0[A$86] extends Semigroup$0[A$86] {

     @abstract
     def empty$6: A$86 = <empty tree>[A$86]

     @final
     @inlineOnce
     @derived(law_leftIdentity$0)
     def law_leftIdentity$1(x$116: A$86): Boolean =
       this.append$3(this.empty$6, x$116) == x$116

     @abstract
     def law_leftIdentity$0(x$110: A$86): Boolean = {
       <empty tree>[Boolean]
     } ensuring {
       (res$77: Boolean) => res$77 && this.law_leftIdentity$1(x$110)
     }

     @final
     @inlineOnce
     @derived(law_rightIdentity$0)
     def law_rightIdentity$2(x$117: A$86): Boolean =
       this.append$3(x$117, this.empty$6) == x$117

     @abstract
     def law_rightIdentity$0(x$111: A$86): Boolean = {
       <empty tree>[Boolean]
     } ensuring {
       (res$80: Boolean) => res$80 && this.law_rightIdentity$2(x$111)
     }

     @law
     def law_associativity$1(x$112: A$86, y$26: A$86, z$12: A$86): Boolean = {
       this.law_associativity$2(x$112, y$26, z$12) && refineLaw$0[A$86](x$112, y$26, z$12)
     } ensuring {
       (res$84: Boolean) => res$84 && this.law_associativity$2(x$112, y$26, z$12)
     }
   }

   @derived(bigIntAdditiveMonoid$0)
   case class $anon$0() extends Monoid$0[BigInt] {

     def empty$7: BigInt = 0
     def append$4(x$114: BigInt, y$27: BigInt): BigInt = x$114 + y$27

     @law
     @derived(law_leftIdentity$0)
     def law_leftIdentity$2(x$119: BigInt): Boolean = {
       true
     } ensuring {
       (res$84: Boolean) => this.law_leftIdentity$1(x$119)
     }

     @law
     def law_rightIdentity$1(x$115: BigInt): Boolean = {
       someProof$0
     } ensuring {
       (res$79: Boolean) => res$79 && this.law_rightIdentity$2(x$115)
     }

     @law
     @derived(law_associativity$0)
     def law_associativity$2(x$120: BigInt, y$29: BigInt, z$13: BigInt): Boolean = {
       true
     } ensuring {
       (res$85: Boolean) => this.law_associativity$1(x$120, y$29, z$13)
     }
   }

   def bigIntAdditiveMonoid$0: Monoid$0[BigInt] = $anon$0()

   def someProof$0: Boolean = true

There are a few things going on here:

1. First of all, each method marked ``@law`` introduces a new method which
   holds the original body of the law. The law's body is then rewritten to
   be empty, and is provided with a postcondition which refers to the newly
   introduced method. This desugaring step basically turns the laws
   into abstract methods which must be overridden at some point with
   methods whose body can be proven to be true, while also satisfying the law
   itself.

   The helper method will be used in subsequent steps to refer to the
   law's body, without having to inline it or call the law itself,
   which is disallowed since it is conceptually an abstract method, as
   evidenced by its newly added ``@abstract`` flag.

   .. code-block:: scala

     // In class `Semigroup`...

     // This is the helper method.
     @final
     @inlineOnce
     @derived(law_associativity$0)
     def law_associativity$2(x$120: A$85, y$30: A$85, z$14: A$85): Boolean = {
       this.append$3(x$120, this.append$3(y$30, z$14)) ==
       this.append$3(this.append$3(x$120, y$30), z$14)
     }

     // This is the original law definition, which now became an abstract method.
     @abstract
     def law_associativity$0(x$109: A$85, y$25: A$85, z$11: A$85): Boolean = {
       <empty tree>[Boolean]
     } ensuring {
       (res$82: Boolean) => res$82 && this.law_associativity$2(x$109, y$25, z$11)
     }

2. Laws which are overridden into abstract subclasses, are provided with a
   postcondition that ensures that their body can be proven true,
   while still satisfying the original law via a call to the helper
   method introduced in the previous step. This step ensures that laws
   cannot be fully redefined, and thus potentially weakened, in subclasses.

   .. code-block:: scala

     // In class `Monoid`...

     @law
     def law_associativity$1(x$112: A$86, y$26: A$86, z$12: A$86): Boolean = {
       this.law_associativity$2(x$112, y$26, z$12) && refineLaw$0[A$86](x$112, y$26, z$12)
     } ensuring {
       (res$84: Boolean) => res$84 && this.law_associativity$2(x$112, y$26, z$12)
     }

3. In the typeclass implementations (eg. class ``$anon$0``), methods which override laws
   are provided with a postcondition which again ensures that their body holds,
   while still satisfying the law they override, again via a call to the helper
   method introduced in step 1.

   .. code-block:: scala

     // In class `$anon$0`...

     @law
     def law_rightIdentity$1(x$115: BigInt): Boolean = {
       someProof$0
     } ensuring {
       (res$79: Boolean) => res$79 && this.law_rightIdentity$2(x$115)
     }

4. If a law is not overridden in a typeclass implementation, a stub override is
   automatically defined by Stainless, to ensure that a verification condition
   will be generated. Those stubs just have ``true`` as a body, and a postcondition
   which calls to the appropriate law helper introduced in step 1.
   This expresses the fact that the law holds on its own, without any additional proof steps.

   .. code-block:: scala

     // In class `$anon$0`

     @law
     @derived(law_leftIdentity$0)
     def law_leftIdentity$2(x$119: BigInt): Boolean = {
       true
     } ensuring {
       (res$84: Boolean) => this.law_leftIdentity$1(x$119)
     }

.. note::

  As can be seen above, calling the super method when refining (such as in ``law_associativity``)
  or proving (such as in ``law_rightIdentity``) a law is superfluous, since it is done anyway
  during the encoding as to ensure that laws cannot be weakened. Doing so can nonetheless help
  readability, since it makes the code match more closely to the semantics of Scala.

.. [WB89] P. Wadler and S. Blott. 1989. How to make ad-hoc polymorphism less ad hoc.

