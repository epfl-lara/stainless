 .. _resourcebounds:

Resource Verification
=====================

Not only does Leon allow verification of correctness properties, it also supports establishing
bounds on resources, such as time or memory usage, consumed by programs. 
The sub-system of Leon that performs verification of resource bounds is called: *Orb*.
It complements the Leon verifier by allowing users to specify and verify 
upper bounds on resources consumed by programs. 


Why Verify Resource Bounds?
---------------------------

Statically proving bounds on resources such as time, and space consumed by softwares is considered too difficult 
a task to accomplish due to the complexities of the hardware, and operating environments that 
the modern day softwares are deployed on.
This is true to an extent only if one wants to precisely estimate the resource usage in terms of the actual
physical units such as wall-clock time or bytes.
However, as shown by decades of research in theoretically computer science, it is possible to asses
resource usage of programs using more abstract, algorithmic metrics that are fairly independent of the runtime
infrastructure.
These metrics often characterize the asymptotic behavior of the programs.
What Leon provides you is a way to establish bounds on such algorithmic metrics. 
For instance, you can state and prove that a function `sorting a list of integers using insertion sort 
takes time quadratic in size of the list`.
After all, most of the  development effort is spent on making implementations efficient, and now you can verify the 
efficiency of your implementations!

The rest of this documentation presents an brief of verifying resource usage of programs using Leon. 
More illustrations are available under the `Resourcebounds` section of `leon web <http://leon.epfl.ch>`_


Proving Abstract Bounds on Resources
------------------------------------

Let us start by considering the function ``count`` shown below that decrements ``n`` until ``0``.
The function takes time `O(n)`, if we consider subtraction of big integers as a constant time operation.
This can be expressed in Leon as shown below:

.. code-block:: scala

  import leon.instrumentation._  
  import leon.invariant._

  object ResourceExample {
    def count(n: BigInt): BigInt = {
     require(n >= 0)
      if(n > 0) count(n - 1)
      else n    
    } ensuring(res => steps <= ? * n + ?)
  }

Consider the postconditions of the ``count`` function.
The postcondition uses a reserved keyword ``steps`` that refers to the number of steps in the evaluation of the function 
``count`` for a given input, 
Generally, it is equal to the number of primitive operations such as arithmetic, logical 
operations performed by the function, and hence is an abstraction of the execution time.
The question marks (``?``) represent unknown coefficients called *holes*, which needs to be inferred by 
the system. 
You will find that Leon is able to automatically infer values for the holes, and complete the bound
as ``steps <= 4 * n + 2``.
This bound is guaranteed to hold for all executions of ``count`` invoked with any ``n``.

Leon also *tries* to ensure that the inferred bounds are as strong as possible. That is, it tries to ensure that
in the inferred bound, the coefficient of a term cannot be reduced without increasing the coefficients of the faster growing terms.
However, the minimality of the inferred constants is only "best-effort", and not guaranteed. 

Importing Inferred Bounds
-------------------------
The `leon web <http://leon.epfl.ch>`_ interface allows importing the inferred resource bounds and correctness invariants (if any),
automatically into the program. To do so, click on a tick mark on the right pane, and choose `import all invariants`.
Once all invariants have been imported, the verification phase will get initiated, which may serve to cross check the results.


Finding Counter-examples for Concrete Bounds
--------------------------------------------

For concrete bounds that do not have holes, Leon can discover counter-examples, which are inputs that violate the specification.
For instance, Leon will report a counter-example on the following code snippet: (Try it here: `leon web <http://leon.epfl.ch>`_)

.. code-block:: scala

  import leon.instrumentation._  
  import leon.invariant._

  object ResourceExample {
    def count(n: BigInt): BigInt = {
     require(n >= 0)
      if(n > 0) count(n - 1)
      else n    
    } ensuring(res => steps <= 2)
  }

The display of the counter-example will consist of an input to the function ``count`` and an output.
The output would be represented as a pair, where the first component refers
to the output of the function, and the second component to its resource usage.
For the above code snippet, Leon would display the following message

.. code-block:: scala

	The following inputs violate the VC:

	n	 := 	BigInt(1)

	It produced the following output:

	(BigInt(0), BigInt(6))

Here, ``BigInt(6)`` is the number of steps taken by the function ``count`` when the input is ``BigInt(1)``.
Clearly, it is not less than 2, and hence violates the specification.
This feature of Leon can be used to manually test the minimality of the bounds once they have been inferred.

Using Correctness Properties to Establish Bounds
------------------------------------------------

Resource bounds can be stated in combination with other correctness properties. 
In fact, sometimes the resource bounds themselves may depend on certain correctness properties.
For example, consider the function ``reverse`` that reverses the elements in a list by calling ``append``.
To upper bound the running time of ``reverse``, we need to know that  ``append`` takes time that is linear
in the size of ``tl`` (which equals ``l.tail``). This holds because the size of list returned by ``reverse(tl)`` is equal to the size of ``tl``. 
These relationships between the sizes of the input and output lists of ``reverse`` and ``append`` can be stated in their postconditions along
with the resource bounds, and will be used during the verification of bounds.

.. code-block:: scala

	import leon.instrumentation._  
	import leon.invariant._
	object ListOperations {
	  sealed abstract class List
	  case class Cons(head: BigInt, tail: List) extends List
	  case class Nil() extends List

	  def size(l: List): BigInt = (l match {
	    case Nil() => 0
	    case Cons(_, t) => 1 + size(t)
	  })

	  def append(l1: List, l2: List): List = (l1 match {
	    case Nil() => l2
	    case Cons(x, xs) => Cons(x, append(xs, l2))

	  }) ensuring (res => size(res) == size(l1) + size(l2) && steps <= ? *size(l1) + ?)

	  def reverse(l: List): List = {
	    l match {
	      case Nil() => l
	      case Cons(hd, tl) => append(reverse(tl), Cons(hd, Nil()))
	    }
	  } ensuring (res => size(res) == size(l) && steps <= ? *(size(l)*size(l)) + ?)
	}

As highlighted by this example, there could be deep inter-relationships between 
the correctness properties, and resource bounds. 
These properties can be seamlessly combined in Leon. 
Given enough correctness properties, Leon can establish resource bounds of complex programs 
like *red-black tree*, *AVL tree*, *binomial heaps*, and many more. 
Some of the benchmarks are available in leon web, others can be found in `testcases/orb-testcases/` directory.

Resources Supported
-------------------

Leon currently supports the following resource bounds, which can be used in the *postcondition* of functions.
Let `f` be a function. The following keywords can be used in its postcondition, and have the following meaning.

* **steps** - Number of steps in the evaluation of the function on a given input. This is an abstraction of time taken by the function on a given input. 
* **alloc** - Number of objects allocated in the heap by the function on a given input. This is an abstraction of heap memory usage
* **stack** - Stack size in words (4 bytes) consumed by the function on a given input. This is an abstraction of stack memory usage
* **depth** - The longest chain of data dependencies between the operations executed by the function on a given input. This is a measure of parallel execution time.
* **rec**   - Number of recursive calls, including mutually recursive calls, executed by the function on a given input. This is similar to a loop count of a single loop. Note that calls to functions that do not belong to the same strongly-connected component (SCC) are not counted by this resource.		  


Dependency on Termination
-------------------------

Proving bounds on resources consumed by a function does not by itself imply termination of the function on all
inputs. More importantly, it is possible to prove invalid bounds for non-terminating functions. 
This holds even for bounds on resources such as `steps`, which counts the number of evaluation steps. 
This constraint is because Leon uses induction over the recursive calls made by a function, which 
is sound only when the function is terminating.
Therefore, users are advised to verify the termination of their programs when proving resource 
or correctness properties. 
In `leon web <http://leon.epfl.ch>`_ you can turn on termination from the *params* memu. 
To run the Leon termination checker from command line  see :ref:`cmdlineoptions`.

Running from Command Line
-------------------------

The resource verifier can be invoked from command line using ``--inferInv`` option.
There are several options that can be supplied to configure the behavior and output of the verifier.
See :ref:`cmdlineoptions` for a detailed list of all the options relevant for resource verification.
A common use case is shown below:

.. code-block:: scala

	./leon --inferInv --minbounds=0 --solvers=orb-smt-z3 ./testcases/orb-testcases/timing/AVLTree.scala

The option ``--inferInv`` invokes the resource verifier. The option ``--minbounds=0``
instructs the verifier to minimize the bounds with a lower bound of 0 for the coefficients. 
The option ``--solvers=orb-smt-z3`` configures the verifier to use the SMT Z3 solver through the 
SMTLIB interface to solve formulas that are generated during inference.
This option is recommended if it is necessary to impose hard time limits on resource verification.


Common Pitfalls 
---------------

* Using non-inductive bounds

	Like in correctness verification, the bounds that need to established  
	must be provable by inducting over the recursive calls made by the program. 
	For instance, the following function has a bound that is not inductive, and hence cannot be proven.

	.. code-block:: scala

	  import leon.instrumentation._  
	  import leon.invariant._

	  object WrongExample {
	    def countUntilN(i: BigInt, n: BigInt): BigInt = {
	     require(n >= i && i >= 0)
	      if(i < n) countUntilN(i + 1, n)
	      else BigInt(0)
	    } ensuring(res => steps <= ? * n + ?)
	  }

	To prove a linear bound for ``countUntilN``, one should use either ``steps <= ? * (n - i) + ?`` or more generally, ``steps <= ? * n + ? * i + ?``
 	

Limitations
-----------

Verification of resource bounds is a significant extension over proving correctness properties.
Unfortunately, certain features that are supported in correctness verification are not supported by resource
verification as yet. Below are a set of features that are not supported currently.

* `xlang` and mutable state
* Higher-order functions and `lazy val`. (To be included in the next update).
* Choose operations
* Class invariants
* Strings
* Bit-vectors, bounded integers: `Int`, `Char`.

References
----------

For more examples, check out the directory ``testcases/orb-testcases/``.
For any questions, please consult  `Ravi Madhavan <http://lara.epfl.ch/~kandhada>`_ and
check the following publications that explain the underlying techniques.

	* `Symbolic resource bound inference for functional programs <http://lara.epfl.ch/~kuncak/papers/MadhavanKuncak14SymbolicResourceBoundInferenceFunctionalPrograms.pdf>`_, by *Ravichandhran Madhavan* and *Viktor Kuncak*. Computer Aided Verification (CAV), 2014.
	* `Verifying Resource Bounds of Programs with Lazy Evaluation and Memoization <https://infoscience.epfl.ch/record/215783>`_, by *Ravichandhran Madhavan*, *Sumith Kulal*, and *Viktor Kuncak*. EPFL Technical Report, 2016.

Contributors
------------

 **Contributor**, **Organization**, **Github Username**

* Ravi Madhavan, EPFL, `ravimad`
* Prateek Fegade (during 2015 Summer), IIT Bombay , `pratikfegade`
* Sumith Kulal (during 2016 Summer), IIT Bombay, `sumith1896`