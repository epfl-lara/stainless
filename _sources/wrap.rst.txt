.. _wrap:

Working With Existing Code
==========================

While the subset of Scala (namely, PureScala) that is currently supported by Stainless
is already expressive enough to implement a lot of different data structures and algorithms,
it is often the case that one would like to avoid re-implementing a piece of code from scratch
in this fragment, but rather re-use some existing code, whether it is part of the codebase or
pulled in from a Java or Scala library.

A wrapper for TrieMap
---------------------

As a running example, let's write a wrapper for the ``scala.collection.concurrent.TrieMap`` class.
A first attempt to wrap it in a regular Stainless datatype could look like the following:

.. code-block:: scala

  import stainless.lang._
  import stainless.annotation._

  import scala.collection.concurrent.TrieMap

  case class TrieMapWrapper[K, V](theMap: TrieMap[K, V])

Unfortunately, this will not work as Stainless will complain that it does not
know about the ``TrieMap`` type. In order to work around this, one can annotate
the field with the ``@extern`` annotation, which tells Stainless that the type
should be treated as opaque.

.. code-block:: scala

  import stainless.lang._
  import stainless.annotation._

  import scala.collection.concurrent.TrieMap
  import scala.collection.concurrent.TrieMap

  case class TrieMapWrapper[K, V](@extern theMap: TrieMap[K, V])

Extern methods
--------------

Let's now define a forwarding method for the ``contains`` method of ``TrieMap``:

.. code-block:: scala

  import stainless.lang._
  import stainless.annotation._

  import scala.collection.concurrent.TrieMap
  import scala.collection.concurrent.TrieMap

  case class TrieMapWrapper[K, V](@extern theMap: TrieMap[K, V]) {

    def contains(k: K): Boolean = {
      theMap contains k
    }
  }

Once again, this will fail because, from Stainless' point of view, ``theMap`` has an opaque type
and thus has no ``contains`` method. By annotating the method itself with ``@extern``, Stainless will
not attempt to extract the method's body, and we can thus freely refer to any of ``TrieMap``'s methods:

.. code-block:: scala

  import stainless.lang._
  import stainless.annotation._

  import scala.collection.concurrent.TrieMap

  case class TrieMapWrapper[K, V](@extern theMap: TrieMap[K, V]) {

    @extern
    def contains(k: K): Boolean = {
      theMap contains k
    }
  }

.. note::
  Methods marked ``@extern`` are allowed to mention types which Stainless is not able to extract.
  Such types will be replaced by the *unknown type* ``?`` during the recovery phase.
  One can inspect which types are replaced during recovery, by supplying the ``--debug=recovery`` flag.

Contracts
---------

Let's also define another extern function, which creates a new empty map:

.. code-block:: scala

  object TrieMapWrapper {
    @extern
    def empty[K, V]: TrieMapWrapper[K, V] = {
      TrieMapWrapper(TrieMap.empty[K, V])
    }
  }

  def prop1 = {
    val wrapper = TrieMapWrapper.empty[Int, String]
    assert(!wrapper.contains(42)) // invalid
  }

Indeed, because Stainless does not know about ``TrieMap.empty``, it cannot assume
by itself that the result of ``TrieMapWrapper.empty`` does not contain any entries.

We can remedy to that by adding a postcondition to the ``empty`` function which says that,
for any key ``k`` of type ``K``, the result of ``TrieMapWrapper.empty`` does not contain the key ``k``.

.. code-block:: scala

  object TrieMapWrapper {
    @extern
    def empty[K, V]: TrieMapWrapper[K, V] = {
      TrieMapWrapper(TrieMap.empty[K, V])
    } ensuring { res =>
      forall((k: K) => !res.contains(k))
    }
  }

The assertion above now verifies successfully.

Purity annotations
------------------

Let's now see what happens when we call ``contains`` twice:

.. code-block:: scala

  def prop1 = {
    val wrapper = TrieMapWrapper.empty[Int, String]
    assert(!wrapper.contains(42))
    assert(!wrapper.contains(42))
  }

.. code-block:: text

    ┌───────────────────┐
  ╔═╡ stainless summary ╞═══════════════════════════════════════════════════╗
  ║ └───────────────────┘                                                   ║
  ║ prop1  body assertion  valid    U:smt-z3  ExternField.scala:46:5  0.018 ║
  ║ prop1  body assertion  invalid  U:smt-z3  ExternField.scala:47:5  0.110 ║
  ╚═════════════════════════════════════════════════════════════════════════╝

The second assertion (perhaps surprisingly) fails to verify. This stems from the fact that Stainless assumes
by default that extern functions and methods mutate their arguments. Indeed, because Stainless
does not know about the body of such methods, it cannot know whether such a function is pure or not.
It is thus up to the user to instruct Stainless otherwise, by annotating the function with ``@pure``:

.. code-block:: scala

  case class TrieMapWrapper[K, V](@extern theMap: TrieMap[K, V]) {

    @extern @pure
    def contains(k: K): Boolean = {
      theMap contains k
    }
  }

With the annotation, the two assertions above now verify:

.. code-block:: text

    ┌───────────────────┐
  ╔═╡ stainless summary ╞═════════════════════════════════════════════════╗
  ║ └───────────────────┘                                                 ║
  ║ prop1  body assertion  valid  U:smt-z3  ExternField.scala:46:5  0.018 ║
  ║ prop1  body assertion  valid  U:smt-z3  ExternField.scala:48:5  0.110 ║
  ╚═══════════════════════════════════════════════════════════════════════╝

We can now define the other methods of interest, with their appropriate contract:

.. code-block:: scala

  import stainless.lang._
  import stainless.annotation._
  import scala.annotation.meta.field

  import scala.collection.concurrent.TrieMap

  case class TrieMapWrapper[K, V](
    @extern
    theMap: TrieMap[K, V]
  ) {

    @extern @pure
    def contains(k: K): Boolean = {
      theMap contains k
    }

    @extern
    def insert(k: K, v: V): Unit = {
      theMap.update(k, v)
    } ensuring {
      this.contains(k) &&
      this.apply(k) == v
    }

    @extern @pure
    def apply(k: K): V = {
      require(contains(k))
      theMap(k)
    }
  }

  object TrieMapWrapper {
    @extern @pure
    def empty[K, V]: TrieMapWrapper[K, V] = {
      TrieMapWrapper(TrieMap.empty[K, V])
    } ensuring { res =>
      forall((k: K) => !res.contains(k))
    }
  }

And we can now reason about our wrapper for ``TrieMap``:

.. code-block:: scala

  def prop2 = {
    val wrapper = TrieMapWrapper.empty[BigInt, String]
    assert(!wrapper.contains(42))
    wrapper.insert(42, "Hello")
    assert(wrapper.contains(42))
    assert(wrapper(42) == "Hello")
  }

.. code-block:: text

    ┌───────────────────┐
  ╔═╡ stainless summary ╞═════════════════════════════════════════════════════════════════════════════════╗
  ║ └───────────────────┘                                                                                 ║
  ║ prop2  body assertion                                 valid  U:smt-z3  ExternField.scala:56:5   0.023 ║
  ║ prop2  body assertion                                 valid  U:smt-z3  ExternField.scala:58:5   0.095 ║
  ║ prop2  body assertion                                 valid  U:smt-z3  ExternField.scala:59:5   0.080 ║
  ║ prop2  precond. (apply[BigInt, String](wrapper, 42))  valid  U:smt-z3  ExternField.scala:59:12  0.200 ║
  ╟-------------------------------------------------------------------------------------------------------╢
  ║ total: 4    valid: 4    (0 from cache) invalid: 0    unknown: 0    time:   0.398                      ║
  ╚═══════════════════════════════════════════════════════════════════════════════════════════════════════╝
