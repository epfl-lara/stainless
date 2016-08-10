 .. _resourcebounds:

Resource Verification
=====================

Not only does Leon allow verification of correctness properties, it also supports establishing
bounds on resources, such as time or memory usage, consumed by programs. 
The sub-system of Leon that performs verification of resource bounds is called: *Orb*, and
is a fairly independent component with a separate project: `Orb <https://github.com/ravimad/Orb2015>`_.
Nonetheless, it is a integral part of the Leon ecosystem that complements the Leon verifier by allowing users to specify and verify 
upper bounds on resources consumed by programs. This is one of the unique feature of the Leon verifier.


Why Verify Resource Bounds?
---------------------------

Statically proving bounds on resources such as time, and space is considered too difficult a task to accomplish
due to complexities of the general purpose hardware, and operating environments that the modern day softwares 
are deployed on.
This is true to an extent only if one wants to precisely estimate the resource usage in terms of the actual
physical unit such as wall-clock time or bytes.
However, as shown by decades of research in theoretically computer science, it is possible to asses
resource usage through more abstract, algorithmic metrics that are fairly independent of the runtime
infrastructure. 
What Orb brings you is an way to establish such algorithmic resource bounds for the implementations
of algorithms. 
For instance, you can state and prove that a function `sorting a list of integers using insertion sort 
takes time quadratic in size of the list`.
The goal of Orb is to allow users to establish that a program works efficiently, and not just correctly, 
because that is where most of the development effort is spent on.

The rest of this documentation presents a brief overview of verifying and inferring resource usages of
programs using Leon. More illustrations are available under the `resourcebounds` section in `leon web <http://leon.epfl.ch>`_

Proving Abstract Bounds on Resources
------------------------------------

Let us start by considering the function `count` shown below that decrements `n` until `0`.
The function takes time `O(n)` assuming that subtraction of big integers takes constant time.
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

Consider the postconditions of the `count` function.
`steps` is a reserved keyword that refers to the number of steps in the evaluation of the function `count` for a given `n`, 
as per the semantics of Scala.
Generally, it is equal to the number of primitive operations such as arithmetic, logical
operations performed by the function. 
The question marks (`?`) represent unknown coefficients called *holes*, which needs to be inferred by 
the system. 
You will find that Leon is able to automatically infer values for the holes, and complete the bound
as `steps <= 4 * n + 2`.
This bound is guaranteed to hold for all executions of `count` invoked with any `n`.

Leon also *tries* to ensure that the inferred bounds are as strong as possible. That is, the coefficients
of a term cannot be reduced without increasing the coefficients of the faster growing terms.
However, the minimality of the inferred constants is only "best-effort", and not guaranteed. 

Finding Counter-examples for Concrete Bounds
--------------------------------------------

Leon can discover counter-examples, which are inputs that violate the specification, for concrete bounds that do not have holes.
This can be use to test the minimality of the bounds once they have been inferred.

Using Correctness Properties to Establish Bounds
------------------------------------------------

Rsesource bounds can be state in combination with other correctness properties. 
Sometimes the resource bounds themselves may depend on certain correctness properties.
For example, consider the function `reverse` that reverses the elements in a list by calling `append`.
To upper bound the running time of `reverse`, we need to know that  `append` is called
on a list whose size is equal to that of `tl`. Otherwise, we would not know how long `append`
will take. This property can be stated in the postcondition of `reverse`, and will be
used during the verification of bounds.
Note that we also need to state the relationship between the sizes of input and output lists 
of `append` in order to establish the `size(res) == size(l)` property of `reverse`.

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
like *red-black tree*, *avl tree*, *binomial heaps*, and many more. 
Some of the benchmarks are available in leon web, others can be found in `testcases/orb-testcases/`` directory.

Resources Supported
-------------------

Leon currently supports the following resource bounds, which can be used in the *postcondition* of functions.
Let `f` be a function. The following keywords can be used in its postcondition, and have the following meaning.

* **steps** - Number of steps in the evaluation of the function on a given input. This is an abstraction of time taken by the function on a given input. 
* **alloc** - Number of objects allocated in the heap by the function on a given input. This is an abstraction of heap memory usage
* **stack** - Stack size in words (4 bytes) consumed by the function on a given input. This is an abstraction of stack memory usage
* **depth** - The longest chain of data dependency between the operations executed by the function on a given input. This is a measure of parallel execution time.
* **rec**   - Number of recursive calls, including mutually recursive calls, executed by the function on a given input. This is similar to a loop count of a single loop. Note that calls to non-recursive functions are not counted in this resource.		  


Dependency on Termination
-------------------------

Proving bounds on resources does not by itself imply termination of the program, and more importantly, 
it is possible to prove invalid bounds on non-terminating programs. 
This holds even for resources such as `steps` that bound the number of steps of execution. 
This constraint is because Leon uses induction over the recursive calls made by a function, which 
is sound only when the function is terminating.
Therefore, users are advised to verify the termination of their programs when proving resource 
or correctness properties. 
In leon web you can turn on termination using the *params* memu. 
To run the Leon termination checker from command line  see :ref:`cmdlineoptions`.

Orb from Command Line
---------------------

The resource verifier can be invoked from command line using: `leon --inferInv` option.
There are several options that can supplied to configure the verifier.
See :ref:`cmdlineoptions` for the command line options relevant for resource verification.

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

	To prove a linear bound for `countUntilN`, one should use either `steps <= ? * (n - i) + ?` or more generally, `steps <= ? * n + ? * i + ?`
 	

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
* Bit-vectors

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

* Ravi Madhavan, EPFL, ravimad  
* Prateek Fegade (during 2015 Summer), IIT Bombay , pratikfegade
* Sumith Kulal (during 2016 Summer), IIT Bombay, Sumith1896