.. _isabelle:

Isabelle
========

Isabelle is an interactive theorem prover. It comes with an IDE where users can
type mathematical specifications and proofs which will be checked continuously.
Specifications consist of a sequence of type and value definitions. All
high-level tools inside Isabelle must justify their proofs and constructions
against a small inference kernel. This greatly diminishes the risk of unsound
proofs.

Additionally, Isabelle features powerful proof automation, for example:

 - classical and equational reasoning
 - decision procedures (e.g. for linear arithmetic)
 - interfaces to automated provers (e.g. Z3 and CVC4)

However, most non-trivial proofs will require the user to give proof hints. In
general, interactive provers like Isabelle trade better guarantees for weaker
automation.

Normally, users write Isabelle specifications manually. Leon comes with a
bridge to Isabelle which allows it to be used as a solver for program
verification.


Installation
------------

You can obtain a copy of Isabelle for your operating system at `its website
<https://isabelle.in.tum.de/>`_, then follow the `installation instructions
<https://isabelle.in.tum.de/installation.html>`_. The installation path needs
to be passed to Leon via the ``--isabelle:base`` command line option. (The path
will end in ``Isabelle2015``. Depending on your operating system, this folder
might be some levels into the installation tree.)

On Linux, you can skip this step. Leon is able to download and install Isabelle
itself. During the first start, you just need to pass the command line option
``--isabelle:download=true``. You may specify ``--isabelle:base``, but don't
have to.

Additionally, you need to instruct Git to fetch all the referenced repositories
via ``git submodule update --init --recursive``.


Basic usage
-----------

For most purposes, Isabelle behaves like any other solver. When running
:ref:`verification`, you can pass ``isabelle`` as a solver (see
:ref:`cmdlineoptions` for details). Isabelle is a bit slower to start up than
the other solvers, so please be patient.


Advanced usage
--------------

Isabelle has some peculiarities. To accomodate for those, there are a set of
specific annotations in the object ``leon.annotation.isabelle``.


Mapping Leon entities to Isabelle entities
******************************************

Isabelle -- or it's standard logic *HOL*, to be precise -- ships with a rather
large existing library. By default, the Isabelle backend would just translate
all Leon definitions into equivalent Isabelle definitions, which means that
existing proofs about them are not applicable. For example, Isabelle/HOL already
has a concatenation function for lists and an associativity proof for it. The
annotations ``@typ``, ``@constructor`` and ``@function`` allow the user to
declare a mapping to existing Isabelle entities. For lists and their append
function, this looks like this:

.. code-block:: scala

   @isabelle.typ(name = "List.list")
   sealed abstract class List[T] {

     @isabelle.function(term = "List.append")
     def ++(that: List[T]): List[T] = (this match {
       case Nil() => that
       case Cons(x, xs) => Cons(x, xs ++ that)
     })

   }

   @isabelle.constructor(name = "List.list.Cons")
   case class Cons[T](h: T, t: List[T]) extends List[T]

   @isabelle.constructor(name = "List.list.Nil")
   case class Nil[T]() extends List[T]

The above is a simplified excerpt from Leon's standard library. However, it is
no problem to map functions with postconditions to their Isabelle equivalents.

By default, mapping for types is loosely checked, whereas mapping for functions
is checked:

 - For types, it is checked that there are exactly as many constructors in Leon
   as in Isabelle and that all constructors are annotated. It is also checked
   that the given constructor names actually exist and that they have the same
   number of arguments, respectively. There is no check whether the field types
   are equivalent. However, in most cases, such a situation would be caught
   later because of type errors.
 
 - For functions, a full equivalence proof is being performed. First, the
   function will be translated to Isabelle as usual. Second, the system will
   try to prove that both definitions are equivalent. If that proof fails, the
   system will emit a warning and ignore the mapping.

The checking behaviour can be influenced with the ``strict`` option (see
:ref:`cmdlineoptions`).


Scripting source files
**********************

The ``script`` annotation allows to embed arbitrary Isabelle text into Leon
source files. In the following example, this is used together with mapping:

.. code-block:: scala

   @isabelle.script(
     name = "Safe_Head",
     source = """
       fun safe_head where
       "safe_head [] = None" |
       "safe_head (x # _) = Some x"
 
       lemma safe_head_eq_head[simp]:
         assumes "~ List.null xs"
         shows "safe_head xs = Some (hd xs)"
       using assms
       by (cases xs) auto
     """
   )
   @isabelle.function(term = "Safe_Head.safe_head")
   def safeHead[A](xs: List[A]): Option[A] = xs match {
     case Nil() => None()
     case Cons(x, _) => Some(x)
   }

``script`` annotations are processed only for functions which are directly or
indirectly referenced from the source file which is under verification by Leon.
The effect of a script is equivalent to defining an Isabelle theory with the
name and content as specified in the annotation, importing the ``Leon`` theory.
Theories created via script annotations must be independent of each other, but
are processed before everything else. As a consequence, any entities defined
in scripts are available for all declarations.

.. note::

   Invalid proofs will raise an error, but skipped proofs (with ``sorry``) are
   not reported.


Proof hints
***********

The system uses a combination of tactics to attempt to prove postconditions of
functions. Should these fail, a custom proof method can be specified with the
``proof`` annotation.

.. code-block:: scala

   @isabelle.proof(method = """(induct "<var xs>", auto)""")
   def flatMapAssoc[A, B, C](xs: List[A], f: A => List[B], g: B => List[C]) =
     (xs.flatMap(f).flatMap(g) == xs.flatMap(x => f(x).flatMap(g))).holds

The method string is interpreted as in Isabelle:

.. code-block:: text

   lemma flatMapAssoc: ...
   by (induct "<var xs>", auto)
 
.. note::

   In annotations, the function parameters are not in scope. That means that
   referring to the actual Scala variable ``xs`` is impossible. Additionally,
   in Isabelle, ``xs`` will not be called ``xs``, but rather ``xs'76`` (with
   the number being globally unique). To be able to refer to ``xs``, the system
   provides the special input syntax ``<var _>``, which turns an identifier
   of a variable into its corresponding variable in Isabelle. Think of it as a
   quotation for Scala in Isabelle. There is also a counterpart for constants:
   ``<const _>``.

The ``proof`` annotations admits a second argument, ``kind``, which specifies a
comma-seperated list of verification conditions it should apply to. The empty
string (default) means all verification conditions.


Influencing the translation of functions
****************************************

By default, the system will only translate the body of a function, that is,
without pre- and postconditions, to Isabelle. Sometimes, the precondition is
required for termination of the function. Since Isabelle doesn't accept
function definitions for which it can't prove termination, the presence of the
precondition is sometimes necessary. This can be achieved by annotating the
function with ``@isabelle.fullBody``. If, for other reasons, termination can't
be proven, the annotation ``@isabelle.noBody`` leaves the function unspecified:
It can still be called from other functions, but no proofs depending on the
outcome of the functions will succeed.


Advanced example
----------------

The following example illustrates the definition of a tail-recursive function.
The challenge when proving correctness for these kinds of functions is that
"simple" induction on the recursive argument is often not sufficient, because
the other arguments change in the recursive calls. Hence, it is prudent to
specify a proof hint. In this example, an induction over the definition of the
``lenTailrec`` function proves the goal:

.. code-block:: scala

   def lenTailrec[T](xs: List[T], n: BigInt): BigInt = xs match {
     case Nil() => n
     case Cons(_, xs) => lenTailrec(xs, 1 + n)
   }

   @isabelle.proof(method = """(induct "<var xs>" "<var n>" rule: [[leon_induct lenTailrec]], auto)""")
   def lemma[A](xs: List[A], n: BigInt) =
     (lenTailrec(xs, n) >= n).holds

The attribute ``[[leon_induct _]]`` summons the induction rule for the
specified function.


Limitations
-----------

 - Mutually-recursive datatypes must be "homogeneous", that is, they all must
   have exactly the same type parameters; otherwise, they cannot be translated.
 - Recursive functions must have at least one declared parameter.
 - Polymorphic recursion is unsupported.
 - The ``const`` and ``leon_induct`` syntax take a mangled identifier name,
   according to the name mangling rules of Scala (and some additional ones).
   The mangling doesn't change the name if it only contains alphanumeric
   characters.
 - The ``const`` and ``leon_induct`` syntax does not work for a given function
   ``f`` if there is another function ``f`` defined anywhere else in the
   program.
