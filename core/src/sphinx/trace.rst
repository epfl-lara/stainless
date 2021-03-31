.. _trace:

Induction and equivalence checking
==================================

Induction and @traceInduct annotation
-------------------------------------

We introduce the @traceInduct annotation for automating proofs using induction. Stainless will transform the annotated lemma by generating the inductive proof, based on the structure of one of the functions that appear in the lemma. This approach is useful for functions that have simple inductive form and are easily mapped into inductive proofs.

Here is one simple example of an equivalence lemma:

.. code-block:: scala

   def zero1(arg: BigInt): BigInt = { 
    if (arg > 0) zero1(arg - 1)
    else BigInt(0)
  }

  def zero2(arg: BigInt): BigInt = {
    BigInt(0)
  }
  
  @traceInduct("")
  def zero_check(arg: BigInt): Boolean = {
    zero1(arg) == zero2(arg)
  }.holds

Without the annotation, Stainless times out when trying to prove equivalence. To help with the proof, the user would have to write more details:

.. code-block:: scala

  def zero_check(arg: BigInt): Boolean = {
    zero1(arg) == zero2(arg)
  }.holds because {
    if (arg > 0) zero_check(arg - 1)
    else true
  }

With @traceInduct annotation, Stainless automatically comes up with a similar proof.


It is possible to specify which function should serve as reference implementation for the inductive proof. This can be done by specifying the reference function name as @traceInduct parameter:

.. code-block:: scala

  def content(l: List[BigInt]): Set[BigInt] = l match {
    case Nil() => Set.empty[BigInt]
    case x::xs => Set(x) ++ content(xs)
  }

  def reverse(l1: List[BigInt], l2: List[BigInt]): List[BigInt] = l1 match {
    case Nil() => l2
    case x::xs => reverse(xs, x::l2)
  }

  @traceInduct("reverse")
  def revPreservesContent(l1: List[BigInt], l2: List[BigInt]): Boolean = {
    content(l1) ++ content(l2) == content(reverse(l1, l2))
  }.holds

Stainless constructs the proof based on the definition of the function reverse, by writing its name as annotation parameter. By induction on l1 and following the structure of the reverse function, Stainless manages to prove this lemma.

Equivalence checking
--------------------

The first example of the previous section shows how @traceInduct annotation can be used to automate equivalence checking for pairs of functions. This way it is possible to verify given implementation by proving equivalence to some reference implementation.

In batched mode, Stainless also supports checking equivalence of larger sets of functions. To avoid writing @traceInduct annotated lemmas for each pair, it is possible to specify the list of functions that we want to check for equivalence. Command line option --comparefuns is used for specifying the list of functions. Command line option --models is used for specifying the list of reference model functions. Those model functions are considered correct and serve as reference implementation for the inductive proof. 

Stainless can automatically generate all the equivalence lemmas and report resulting equivalence classes. This is done by checking for eqivalence of each function from the --comparefuns list and each model function from the --models list, until the proof of equvalence or a counter example is found for one of the models.

For example, when running Stainless with the following options (assuming that the file zero.scala contains functions f1, f2, f3, m1 and m2):

.. code-block:: bash

  $ stainless file.scala --batched=true --comparefuns=f1,f2,f3 --models=m1,m2 --timeout=5

Stainless will try to prove equivalence for the following pairs of functions, assuming that f1 and f3 are equivalent to m1, and f2 is equivalent to m2 (but not m1):

- f1 == m1 (verifies, no need to check for f1 == m2)
- f2 == m1
- f2 == m2
- f3 == m1 (verifies, no need to check for f3 == m2)
