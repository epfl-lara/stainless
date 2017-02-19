.. _cmdlineoptions:

Command Line Options
====================

Stainless's command line options have the form ``--option`` or ``--option=value``.
To enable a flag option, use ``--option=true`` or ``on`` or ``yes``,
or just ``--option``. To disable a flag option, use ``--option=false``
or ``off`` or ``no``.

Additionally, if you need to pass options to the ``scalac`` frontend of Stainless,
you can do it by using a single dash ``-``. For example, try ``-Ybrowse:typer``.

The rest of this section presents command-line options that Stainless recognizes.
For a short (but always up-to-date) summary, you can also invoke ``leon --help``.

Choosing which Stainless feature to use
---------------------------------------

The first group of options determine which feature of Stainless will be used.
These options are mutually exclusive (except when noted). By default, ``--verification`` is chosen.

* ``--verification``

  Proves or disproves function contracts, as explained in the `Verification <verification.rst>`_ section.

* ``--termination``

  Runs termination analysis. Can be used along ``--verify``.

* ``--help``

  Prints a helpful message, then exits.


Additional top-level options
----------------------------

These options are available to all Stainless components:

* ``--debug=d1,d2,...``

  Enables printing detailed messages for the components d1,d2,... .
  Available components are:

  * ``solver`` (SMT solvers and their wrappers)

  * ``termination`` (Termination analysis)

  * ``timers`` (Timers, timer pools)

  * ``trees`` (Manipulation of trees)

  * ``verification`` (Verification)

* ``--functions=f1,f2,...``

  Only consider functions f1, f2, ... . This applies to all functionalities
  where Stainless manipulates the input in a per-function basis.

  Stainless will match against suffixes of qualified names. For instance:
  ``--functions=List.size`` will match the method ``leon.collection.List.size``,
  while  ``--functions=size`` will match all methods and functions named ``size``.
  This option supports ``_`` as wildcard: ``--functions=List._`` will
  match all ``List`` methods.

* ``--solvers=s1,s2,...``

  Use solvers s1, s2,... . If more than one solver is chosen, all chosen
  solvers will be used in parallel, and the best result will be presented.
  By default, the ``nativez3`` solver is picked.

  Some solvers are specialized in proving verification conditions
  and will have hard time finding a counterexample in case of an invalid
  verification condition, whereas some are specialized in finding
  counterexamples, and some provide a compromise between the two.
  Also, some solvers do not as of now support higher-order functions.

  Available solvers include:

  * ``nativez3``

    Native Z3 with z3-templates for unfolding recursive functions (default).

  * ``smt-cvc4``

    CVC4 through SMT-LIB. An algorithm within Stainless takes up the unfolding
    of recursive functions, handling of lambdas etc. To use this or any
    of the following CVC4-based solvers, you need to have the ``cvc4``
    executable in your system path (the latest unstable version is recommended).

  * ``smt-z3``

    Z3 through SMT-LIB. To use this or the next solver, you need to
    have the ``z3`` executable in your program path (the latest stable version
    is recommended). Inductive reasoning happens on the Stainless side
    (similarly to ``smt-cvc4``).

  * ``unrollz3``

    Native Z3, but inductive reasoning happens within Stainless (similarly to ``smt-z3``).

  * ``princess``

    Princess solver through its native interface (uses princess-templates) during
    unfolding. This is a full-stack JVM solver and enables Stainless to run with
    no external solver dependencies.

* ``--timeout=t``

  Set a timeout for each attempt to prove one verification condition/
  repair one function (in sec.)

Additional Options (by component)
---------------------------------

The following options relate to specific components in Stainless.

Verification
************

* ``--parallelvcs``

  Check verification conditions in parallel.

* ``--failearly``

  Aborts verification as soon as an invalid VC is found.

Termination
***********

* ``--ignoreposts``

  Ignore postconditions during termination verification.

Unrolling Solver
****************

* ``--checkmodels``

  Double-check counterexamples with evaluator.

* ``--feelinglucky``

  Use evaluator to find counterexamples early.

* ``--unrollassumptions``

  Use unsat-assumptions to drive unrolling while remaining fair.

* ``--silenterrors``

  Don't crash on errors, simply return ``Unknown``.

* ``--unrollfactor=n``

  Speeds up unrolling by a factor ``n``.

* ``--modelfinding=n``

  Boosts model-finding capabilities by a factor ``n``. This may come at
  the cost of proof construction.

* ``--nosimplifications``

  Disables program simplification heuristics.

CVC4 Solver
***********

* ``--solver:cvc4=<cvc4-opt>``

  Pass extra command-line arguments to CVC4.

Evaluators
**********

* ``--codegen``

  Use compiled evaluator instead of interpreter.

* ``--smallarrays``

  Assume all arrays can fit into memory during compiled evaluation.

* ``--instrument``

  Instrument ADT field access during code generation.

* ``--maxcalls=n``

  Bounds the total number of function call evaluations (before crashing).

* ``--ignorecontracts``

  Ignores function contracts during evaluation.

