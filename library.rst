.. _library:

Leon Library
============

Leon defines its own versions of most data structures. One
of the reasons is to ensure that these operations can be
correctly mapped to mathematical functions and relations
inside of SMT solvers, largely defined by the SMT-LIB
standard (see http://www.smt-lib.org/).

To use Leon's libraries, you need to use the appropriate
`import` directive at the top of Leon's compilation units.
Here is a quick summary of what to import.

+--------------------------------+----------------------------------------------------+
| Package to import              | What it gives access to                            |
+================================+====================================================+
| `leon.annotation`              | Leon annotations, e.g. @induct                     |
+--------------------------------+----------------------------------------------------+
| `leon.lang`                    | `Map`, `Set`, `holds`, `passes`, `invariant`       |
+--------------------------------+----------------------------------------------------+
| `leon.collection._`            | List[T] and subclasses, Option[T] and subclasses   |
+--------------------------------+----------------------------------------------------+
| `leon.lang.string`             | String                                             |
+--------------------------------+----------------------------------------------------+
| `leon.lang.xlang`              | epsilon                                            |
+--------------------------------+----------------------------------------------------+
| `leon.lang.synthesis`          | choose, ???, ?, ?!                                 |
+--------------------------------+----------------------------------------------------+

To learn more, we encourage you to
look in the `library/` subdirectory of Leon distribution.

Annotations
-----------

Leon provides some special annotations in the package ``leon.annotation``,
which instruct Leon to handle some functions or objects in a specialized way.

+-------------------+---------------------------------------------------+
| Annotation        | Meaning                                           |
+===================+===================================================+
| ``@library``      | Treat this object/function as library, don't try  |
|                   | to verify its specification. Can be overriden by  |
|                   | including a function name in the ``--functions``  |
|                   | command line option.                              |
+-------------------+---------------------------------------------------+
| ``@induct``       | Use the inductive tactic when generating          |
|                   | verification conditions.                          |
+-------------------+---------------------------------------------------+
| ``@ignore``       | Ignore this definition when extracting Leon trees.|
|                   | This annotation is useful to define functions     |
|                   | that are not in Leon's language but will be       |
|                   | hard-coded into specialized trees, or to include  |
|                   | code written in full Scala which is not verifiable|
|                   | by Leon.                                          |
+-------------------+---------------------------------------------------+


List[T]
-------

As there is no special support for Lists in SMT solvers, Leon Lists are encoded
as an ordinary algebraic data type:

.. code-block:: scala

  sealed abstract class List[T]
  case class Cons[T](h: T, t: List[T]) extends List[T]
  case class Nil[T]() extends List[T]


List API
********

Leon Lists support a rich and strongly specified API.

+---------------------------------------------------+---------------------------------------------------+
| Method signature for ``List[T]``                  | Short description                                 |
+===================================================+===================================================+
| ``size: BigInt``                                  | Number of elements in this List.                  |
+---------------------------------------------------+---------------------------------------------------+
| ``content: Set[T]``                               | The set of elements in this List.                 |  
+---------------------------------------------------+---------------------------------------------------+
| ``contains(v: T): Boolean``                       | Returns true if this List contains ``v``.         |
+---------------------------------------------------+---------------------------------------------------+
| ``++(that: List[T]): List[T]``                    | Append this List with ``that``.                   |
+---------------------------------------------------+---------------------------------------------------+
| ``head: T``                                       | Returns the head of this List. Can only be called |
|                                                   | on a nonempty List.                               |
+---------------------------------------------------+---------------------------------------------------+
| ``tail: List[T]``                                 | Returns the tail of this List. Can only be called |
|                                                   | on a nonempty List.                               |
+---------------------------------------------------+---------------------------------------------------+
| ``apply(index: BigInt): T``                       | Return the element in index ``index`` in this     |
|                                                   | List (0-indexed).                                 |
+---------------------------------------------------+---------------------------------------------------+
| ``::(t:T): List[T]``                              | Prepend an element to this List.                  |
+---------------------------------------------------+---------------------------------------------------+
| ``:+(t:T): List[T]``                              | Append an element to this List.                   |
+---------------------------------------------------+---------------------------------------------------+
| ``reverse: List[T]``                              | The reverse of this List.                         |
+---------------------------------------------------+---------------------------------------------------+
| ``take(i: BigInt): List[T]``                      | Take the first ``i`` elements of this List, or    |
|                                                   | the whole List if it has less than ``i`` elements.|
+---------------------------------------------------+---------------------------------------------------+
| ``drop(i: BigInt): List[T]``                      | This List without the first ``i`` elements,       |
|                                                   | or the Nil() if this List has less than ``i``     |
|                                                   | elements.                                         |
+---------------------------------------------------+---------------------------------------------------+
| ``slice(from: BigInt, to: BigInt): List[T]``      | Take a sublist of this List, from index ``from``  |
|                                                   | to index ``to``.                                  |
+---------------------------------------------------+---------------------------------------------------+
| ``replace(from: T, to: T): List[T]``              | Replace all occurrences of ``from`` in this List  |
|                                                   | with ``to``.                                      |
+---------------------------------------------------+---------------------------------------------------+
| ``chunks(s: BigInt): List[List[T]]``              |                                                   |
+---------------------------------------------------+---------------------------------------------------+
| ``zip[B](that: List[B]): List[(T, B)]``           | Zip this list with ``that``. In case the Lists    |
|                                                   | do not have equal size, take a prefix of the      |
|                                                   | longer.                                           |
+---------------------------------------------------+---------------------------------------------------+
| ``-(e: T): List[T]``                              | Remove all occurrences of ``e`` from this List.   |
+---------------------------------------------------+---------------------------------------------------+
| ``--(that: List[T]): List[T]``                    | Remove all occurrences of any element in ``that`` |
|                                                   | from this List.                                   |
+---------------------------------------------------+---------------------------------------------------+
| ``&(that: List[T]): List[T]``                     | A list of all elements that occur both in         |
|                                                   | ``that`` and this List.                           |
+---------------------------------------------------+---------------------------------------------------+
| ``pad(s: BigInt, e: T): List[T]``                 | Add ``s`` instances of ``e`` at the end of this   |
|                                                   | List.                                             |
+---------------------------------------------------+---------------------------------------------------+
| ``find(e: T): Option[BigInt]``                    | Look for the element ``e`` in this List, and      | 
|                                                   | optionally return its index if it is found.       |
+---------------------------------------------------+---------------------------------------------------+
| ``init: List[T]``                                 | Return this List except the last element.         |
|                                                   | Can only be called on nonempty Lists.             |
+---------------------------------------------------+---------------------------------------------------+
| ``last: T``                                       | Return the last element of this List.             |
|                                                   | Can only be called on nonempty Lists.             |
+---------------------------------------------------+---------------------------------------------------+
| ``lastOption: Option[T]``                         | Optionally return the last element of this List.  |
+---------------------------------------------------+---------------------------------------------------+
| ``headOption: Option[T]``                         | Optionally return the first element of this List. |
+---------------------------------------------------+---------------------------------------------------+
| ``unique: List[T]``                               | Return this List without duplicates.              |
+---------------------------------------------------+---------------------------------------------------+
| ``splitAt(e: T): List[List[T]]``                  | Split this List to chunks separated by an         |
|                                                   | occurrence of ``e``.                              |
+---------------------------------------------------+---------------------------------------------------+
| ``split(seps: List[T]): List[List[T]]``           | Split this List in chunks separated by an         |
|                                                   | occurrence of any element in ``seps``.            |
+---------------------------------------------------+---------------------------------------------------+
| ``count(e: T): BigInt``                           | Count the occurrences of ``e`` in this List.      |
+---------------------------------------------------+---------------------------------------------------+
| ``evenSplit: (List[T], List[T])``                 | Split this List in two halves.                    |
+---------------------------------------------------+---------------------------------------------------+
| ``insertAt(pos: BigInt, l: List[T]): List[T]``    | Insert an element after index ``pos`` in this     |
|                                                   | List.                                             |
+---------------------------------------------------+---------------------------------------------------+
| ``replaceAt(pos: BigInt, l: List[T]): List[T]``   | Replace the ``l.size`` elements after index       |
|                                                   | ``pos``, or all elements after index ``pos``      |
|                                                   | if there are not enough elements,                 |
|                                                   | with the elements in ``l``.                       |
+---------------------------------------------------+---------------------------------------------------+
| ``rotate(s: BigInt): List[T]``                    | Rotate this list by ``s`` positions.              |
+---------------------------------------------------+---------------------------------------------------+
| ``isEmpty: Boolean``                              | Returns whether this List is empty.               |
+---------------------------------------------------+---------------------------------------------------+
| ``map[R](f: T => R): List[R]``                    | Builds a new List by applying a predicate ``f``   |
|                                                   | to all elements of this list.                     |
+---------------------------------------------------+---------------------------------------------------+
| ``foldLeft[R](z: R)(f: (R,T) => R): R``           | Applies the binary operator ``f`` to a start value| 
|                                                   | ``z`` and all elements of this List, going left   |
|                                                   | to right.                                         |
+---------------------------------------------------+---------------------------------------------------+
| ``foldRight[R](f: (T,R) => R)(z: R): R``          | Applies a binary operator ``f`` to all elements of|  
|                                                   | this list and a start value ``z``, going right to |
|                                                   | left.                                             |
+---------------------------------------------------+---------------------------------------------------+
| ``scanLeft[R](z: R)(f: (R,T) => R): List[R]``     | Produces a List containing cumulative results     |
|                                                   | of applying the operator ``f`` going left to      |
|                                                   | right.                                            |
+---------------------------------------------------+---------------------------------------------------+
| ``scanRight[R](f: (T,R) => R)(z: R): List[R]``    | Produces a List containing cumulative results     |
|                                                   | of applying the operator ``f`` going right to     |
|                                                   | left.                                             |
+---------------------------------------------------+---------------------------------------------------+
| ``flatMap[R](f: T => List[R]): List[R]``          | Builds a new List by applying a function ``f``    |
|                                                   | to all elements of this list and using the        |
|                                                   | elements of the resulting Lists.                  |
+---------------------------------------------------+---------------------------------------------------+
| ``filter(p: T => Boolean): List[T]``              | Selects all elements of this List                 |
|                                                   | which satisfy the predicate ``p``                 |
+---------------------------------------------------+---------------------------------------------------+
| ``forall(p: T => Boolean): Boolean``              | Tests whether predicate ``p`` holds               |
|                                                   | for all elements of this List.                    |
+---------------------------------------------------+---------------------------------------------------+
| ``exists(p: T => Boolean): Boolean``              | Tests whether predicate ``p``  holds for some of  |
|                                                   | the elements of this List.                        |
+---------------------------------------------------+---------------------------------------------------+
| ``find(p: T => Boolean): Option[T]``              | Finds the first element of this List satisfying   |
|                                                   | predicate ``p``, if any.                          |
+---------------------------------------------------+---------------------------------------------------+
| ``takeWhile(p: T => Boolean): List[T]``           | Takes longest prefix of elements that satisfy     |
|                                                   | predicate ``p``                                   |
+---------------------------------------------------+---------------------------------------------------+

List.apply(e: T*)
*****************

It is possible to create Lists with varargs like in regular Scala,
for example ``List(1,2,3)`` or ``List()``. This expression will be 
desugared into a series of applications of ``Cons``.

Additional operations on Lists
******************************

The object ``ListOps`` offers this additional operations:

+--------------------------------------------------------+---------------------------------------------------+
| Function signature                                     | Short description                                 |
+========================================================+===================================================+
| ``flatten[T](ls: List[List[T]]): List[T]``             | Converts the List of Lists ``ls`` into a List     |
|                                                        | formed by the elements of these Lists.            |
+--------------------------------------------------------+---------------------------------------------------+
| ``isSorted(ls: List[BigInt]): Boolean``                | Returns whether this list of mathematical integers|
|                                                        | is sorted in ascending order.                     |
+--------------------------------------------------------+---------------------------------------------------+
| ``sorted(ls: List[BigInt]): List[BigInt]``             | Sorts this list of mathematical integers          |
|                                                        | is sorted in ascending order.                     |
+--------------------------------------------------------+---------------------------------------------------+
| ``insSort(ls: List[BigInt], v: BigInt): List[BigInt]`` | Sorts this list of mathematical integers          |
|                                                        | is sorted in ascending order using insertion sort.|
+--------------------------------------------------------+---------------------------------------------------+

Theorems on Lists
*****************

The following theorems on Lists have been proven by Leon and are included 
in the object ``ListSpecs``:

+---------------------------------------------------------------+--------------------------------------------------------+
| Theorem signature                                             | Proven Claim                                           |
+===============================================================+========================================================+
| ``snocIndex[T](l : List[T], t : T, i : BigInt)``              | ``(l :+ t).apply(i) == (if (i < l.size) l(i) else t)`` |
+---------------------------------------------------------------+--------------------------------------------------------+
| ``reverseIndex[T](l : List[T], i : BigInt)``                  | ``l.reverse.apply(i) == l.apply(l.size - 1 - i)``      |
+---------------------------------------------------------------+--------------------------------------------------------+
| ``appendIndex[T](l1 : List[T], l2 : List[T], i : BigInt)``    | ``(l1 ++ l2).apply(i) ==``                             |
|                                                               | ``(if (i < l1.size) l1(i) else l2(i - l1.size))``      |
+---------------------------------------------------------------+--------------------------------------------------------+
| ``appendAssoc[T](l1 : List[T], l2 : List[T], l3 : List[T])``  | ``((l1 ++ l2) ++ l3) == (l1 ++ (l2 ++ l3))``           |
+---------------------------------------------------------------+--------------------------------------------------------+
| ``snocIsAppend[T](l : List[T], t : T)``                       | ``(l :+ t) == l ++ Cons[T](t, Nil())``                 |
+---------------------------------------------------------------+--------------------------------------------------------+
| ``snocAfterAppend[T](l1 : List[T], l2 : List[T], t : T)``     | ``(l1 ++ l2) :+ t == (l1 ++ (l2 :+ t))``               |
+---------------------------------------------------------------+--------------------------------------------------------+
| ``snocReverse[T](l : List[T], t : T)``                        | ``(l :+ t).reverse == Cons(t, l.reverse)``             |
+---------------------------------------------------------------+--------------------------------------------------------+
| ``reverseReverse[T](l : List[T])``                            | ``l.reverse.reverse == l``                             |
+---------------------------------------------------------------+--------------------------------------------------------+
| ``scanVsFoldRight[A,B](l: List[A], z: B, f: (A,B) => B)``     | ``l.scanRight(f)(z).head == l.foldRight(f)(z)``        |
+---------------------------------------------------------------+--------------------------------------------------------+

Set[T], Map[T]
--------------

Leon uses its own Sets and Maps, which are defined in the ``leon.lang`` package.
However, these classes are are not implemented within Leon.
Instead, they are parsed into specialized trees.
Methods of these classes are mapped to specialized trees within SMT solvers.
For code generation, we rely on Java Sets and Maps.

The API of these classes is a subset of the Scala API and can be found
in the :ref:`purescala` section.

Additionally, the following functions for Sets are provided in the
``leon.collection`` package:


+-----------------------------------------------------------+-------------------------------------------+
| Function signature                                        | Short description                         |
+===========================================================+===========================================+
| ``setToList[A](set: Set[A]): List[A]``                    | Transforms the Set ``set`` into a List.   |
+-----------------------------------------------------------+-------------------------------------------+
| ``setForall[A](set: Set[A], p: A => Boolean): Boolean``   | Tests whether predicate ``p`` holds       |
|                                                           | for all elements of Set ``set``.          |
+-----------------------------------------------------------+-------------------------------------------+
| ``setExists[A](set: Set[A], p: A => Boolean): Boolean``   | Tests whether predicate ``p`` holds       |
|                                                           | for all elements of Set ``set``.          |
+-----------------------------------------------------------+-------------------------------------------+

