.. equivalence:

Equivalence Checking
====================

Stainless can prove equivalence of recursive programs using automated functional induction. Additionaly, it can treat many programs at once, reusing the information obtained throughout the process, to reason about subsequent programs. `This
<https://infoscience.epfl.ch/record/290689?&ln=en>`_ technical report explains the underlying algorithms.

To run the equivalence checker, use the ``--batched`` option of Stainless. The option ``--comparefuns`` specifies the names of candidate functions. The option ``--models`` specifies the names of reference functions.


Example run
-----------

Consider the following three functions ``isSortedA`` (incorrect), ``isSortedB`` and ``isSortedC`` (both correct), that implement a check whether a given input list is sorted in a non-decreasing order:

.. code-block:: scala

  def isSortedA(l: List[Int]): Boolean = {
    def leq(cur: Int, next: Int): Boolean = cur < next
    def iter(l: List[Int]): Boolean =
      if (l.isEmpty) true
      else if (l.tail.isEmpty) true
      else leq(l.head, l.tail.head) && iter(l.tail) 
    if (l.size < 2) true
    else l.head <= l.tail.head && iter(l.tail)
  }

.. code-block:: scala

  def isSortedB(l: List[Int]): Boolean = {
    if (l.isEmpty)
      true
    else if (!l.tail.isEmpty && l.head > l.tail.head)
      false
    else 
      isSortedB(l.tail)
  }

.. code-block:: scala

  def isSortedC(l: List[Int]): Boolean = {
    def chk(l: List[Int], p: Int, a: Boolean): Boolean = {
      if (l.isEmpty) a
      else if (l.head < p) false
      else chk(l.tail, l.head, a)
    }
    if (l.isEmpty) true
    else chk(l, l.head, true)
  }

And the following reference function ``isSortedR``:

.. code-block:: scala

  def isSortedR(l: List[Int]): Boolean = {
    def loop(p: Int, l: List[Int]): Boolean = l match {
      case Nil() => true
      case Cons(x, xs) if (p <= x) => loop(x, xs)
      case _ => false
    }
    if (l.isEmpty) true
    else loop(l.head, l.tail)
  }

The following command invokes the equivalence checking, assuming that all those functions are stored in ``isSorted.scala``:

``stainless isSorted.scala --batched=true --comparefuns=isSortedA,isSortedB,isSortedC --models=isSortedR --timeout=1``

Stainless automatically generates all the equivalence lemmas and reports resulting equivalence clusters. This is done by checking for equivalence of each function from the ``--comparefuns`` list against the model functions from the ``--models`` list, until the proof of equivalence or a counterexample is found for one of the models.

The output of equivalence checking is a classification of candidate functions into the following categories:

 - ``Wrong``, if the signature is wrong;
 - ``Correct``, if there is a reference program provably equivalent to this program;
 - ``Incorrect``, if there is a counterexample that disproves the equivalence; 
 - ``Unknown``, when there is neither a proof nor a counterexample of equivalence.  

For our example run, we get the following output:

.. code-block:: text

    [  Info  ] Printing equivalence checking results:
    [  Info  ] List of functions that are equivalent to model IsSorted.isSortedR: IsSorted.isSortedB
    [  Info  ] List of functions that are equivalent to model IsSorted.isSortedB: IsSorted.isSortedC
    [  Info  ] List of erroneous functions: IsSorted.isSortedA
    [  Info  ] List of timed-out functions: 
    [  Info  ] List of wrong functions: 
    [  Info  ] Printing the final state:
    [  Info  ] Path for the function IsSorted.isSortedB: IsSorted.isSortedR
    [  Info  ] Path for the function IsSorted.isSortedA: IsSorted.isSortedR
    [  Info  ] Path for the function IsSorted.isSortedC: IsSorted.isSortedB, IsSorted.isSortedR
    [  Info  ] Counterexample for the function IsSorted.isSortedA: Map(l -> Cons[Int](-2135752701, Cons[Int](11730945, Cons[Int](11730945, Nil[Int]()))))
