.. _cmdlineoptions:

Command Line Options
====================

Leon's command line options have the form ``--option`` or ``--option=value``.
To enable a flag option, use ``--option=true`` or ``on`` or ``yes``,
or just ``--option``. To disable a flag option, use ``--option=false``
or ``off`` or ``no``.

Additionally, if you need to pass options to the ``scalac`` frontend of Leon,
you can do it by using a single dash ``-``. For example, ``-Ybrowse:typer``.

The rest of this section presents command-line options that Leon recognizes.
For more up-to-date list, please invoke ``leon --help``.

Choosing which Leon feature to use
----------------------------------

The first group of options determine which feature of Leon will be used.
These options are mutually exclusive. By default, ``--verify`` is chosen.

* ``--eval`` 
 
  Evaluates parameterless functions and value definitions.
  
* ``--verify``
  
  Proves or disproves function contracts, as explained in the :ref:`verification` section.

* ``--repair``
  
  Runs program :ref:`repair <repair>`.
  
* ``--synthesis``
  
  Partially synthesizes ``choose()`` constructs (see :ref:`synthesis` section).

* ``--termination``
  
  Runs termination analysis. Can be used along ``--verify``.

* ``--inferInv`` 

  Infer invariants from (instrumented) the code (using Orb)

* ``--instrument``                

  Instrument the code for inferring time/depth/stack bounds (using Orb)

* ``--noop``
  
  Runs the program through the extraction and preprocessing phases, then outputs it in the specified
  directory. Used mostly for debugging purposes.

* ``--help``
  
  Prints a helpful message, then exits.



Additional top-level options
----------------------------

These options are available by all Leon components:

* ``--debug=d1,d2,...``
  
  Enables printing detailed messages for the components d1,d2,... .
  Available components are: 

  * ``datagen`` (Data generators)
  
  * ``eval`` (Evaluators)
  
  * ``leon`` (The top-level component)
  
  * ``options`` (Options parsed by Leon)
  
  * ``repair`` (Program repair)
  
  * ``solver`` (SMT solvers and their wrappers)
  
  * ``synthesis`` (Program synthesis)
  
  * ``termination`` (Termination analysis)
  
  * ``timers`` (Timers, timer pools)
  
  * ``trees`` (Manipulation of trees)
  
  * ``verification`` (Verification)
  
  * ``xlang`` (Transformation of XLang into Pure Scala programs)


* ``--functions=f1,f2,...``
  
  Only consider functions f1, f2, ... . This applies to all functionalities 
  where Leon manipulates the input in a per-function basis.

  Leon will match against suffixes of qualified names. For instance:
  ``--functions=List.size`` will match the method
  ``leon.collection.List.size`` while  ``--functions=size`` will match all ``size``
  methods and functions. This option supports ``_`` as wildcard: ``--functions=List._`` will
  match all ``List`` methods.

* ``--solvers=s1,s2,...`` 
  
  Use solvers s1, s2,... . If more than one solver is chosen, all chosen 
  solvers will be used in parallel, and the best result will be presented.
  By default, the ``fairz3`` solver is picked.
 
  Some solvers are specialized in proving verification conditions 
  and will have hard time finding a counterexample in case of an invalid 
  verification condition, whereas some are specialized in finding
  counterexamples, and some provide a compromise between the two.
  Also, some solvers do not as of now support higher-order functions.

  Available solvers include:
  
  * ``enum`` 
    
    Uses enumeration-based techniques to discover counterexamples.
    This solver does not actually invoke an SMT solver,
    and operates entirely on the level of Leon trees.

  * ``fairz3``

    Native Z3 with z3-templates for unfolding recursive functions (default).
  
  * ``smt-cvc4``
    
    CVC4 through SMT-LIB. An algorithm within Leon takes up the unfolding 
    of recursive functions, handling of lambdas etc. To use this or any 
    of the following CVC4-based solvers, you need to have the ``cvc4``
    executable in your system path (the latest unstable version is recommended).
  
  * ``smt-cvc4-cex``
 
    CVC4 through SMT-LIB, in-solver finite-model-finding, for counter-examples only.
    Recursive functions are not unrolled, but encoded through the
    ``define-funs-rec`` construct available in the new SMTLIB-2.5 standard.
    Currently, this solver does not handle higher-order functions.
  
  * ``smt-cvc4-proof``
   
    CVC4 through SMT-LIB, for proofs only. Functions are encoded as in 
    ``smt-cvc4-cex``.
    Currently, this solver does not handle higher-order functions.
  
  * ``smt-z3``
   
    Z3 through SMT-LIB. To use this or the next solver, you need to 
    have the ``z3`` executable in your program path (the latest stable version
    is recommended). Inductive reasoning happens on the Leon side
    (similarly to ``smt-cvc4``).
  
  * ``smt-z3-q``
   
    Z3 through SMT-LIB, but (recursive) functions are not unrolled and are 
    instead encoded with universal quantification.
    For example, ``def foo(x:A) = e`` would be encoded by asserting
    
    .. math::
    
      \forall (x:A). foo(x) = e

    even if ``e`` contains an invocation to ``foo``.

    Currently, this solver does not handle higher-order functions.
  
  * ``unrollz3``
    
    Native Z3, but inductive reasoning happens within Leon (similarly to ``smt-z3``).

  * ``ground``

    Only solves ground verification conditions (without variables) by evaluating them.

  * ``isabelle``

    Solve verification conditions via Isabelle.
  
* ``--strict``

  Terminate Leon after each phase if a non-fatal error is encountered 
  (such as a failed verification condition). By default, this option is activated.

* ``--timeout=t``

  Set a timeout for each attempt to prove one verification condition/
  repair one function (in sec.)
    
* ``--xlang``
  
  Support for additional language constructs described in :ref:`xlang`.
  These constructs are desugared into :ref:`purescala` before other operations.

Invariant Inference
-------------------

These options are to be used in conjuction with ``--inferInv`` and ``--instrument``.

* ``--cegis``

  Use cegis instead of farkas

* ``--disableInfer``

  Disable automatic inference of auxiliary invariants

* ``--fullunroll``

  Unroll all calls in every unroll step

* ``--inferTemp``

  Infer templates by enumeration

* ``--minbounds``

  Tighten the inferred time bounds

* ``--stats-suffix=s``

  Specifies the suffix of the statistics file

* ``--usereals``

  Interpret the input program as a program over real numbers

* ``--wholeprogram``

  Perform a non-modular whole program analysis

* ``--withmult``

  Do not convert multiplication into a recursive function inside verification conditions

Additional Options (by component)
---------------------------------

File Output
***********

* ``--o=dir``
  
  Output files to the directory ``dir`` (default: leon.out).
  Used when ``--noop`` is selected.

Code Extraction
***************

* ``--strictCompilation``

  Do not try to recover after an error in compilation and exit Leon.

Synthesis
*********

These options are also used by repair during the synthesis stage.

* ``--cegis:opttimeout``

  Consider a time-out of CE-search as untrusted solution.

* ``--cegis:shrink``

  Shrink non-deterministic programs when tests pruning works well.

* ``--cegis:vanuatoo``
 
  Generate inputs using new korat-style generator.
  
* ``--costmodel=cm``
  
  Use a specific cost model for this search.
  Available: ``Naive``, ``WeightedBranches``

* ``--derivtrees``
  
  Generate a derivation tree for every synthesized function.
  The trees will be output in ``*.dot`` files.

* ``--manual=cmd``
  
  Override Leon's automated search through the space of programs during synthesis.
  Instead, the user can navigate the program space manually
  by choosing which deductive synthesis rules is instantiated each time.

  The optional ``cmd`` argument is a series of natural numbers in the form
  ``n1,n1,...,nk``. It represents the series of command indexes that the search
  should instantiate at the beginning of the search.
  Useful for repeated search attempts.

Fair-z3 Solver
**************

* ``--checkmodels``

  Double-check counter-examples with evaluator.

* ``--codegen``
  
  Use compiled evaluator instead of interpreter.

* ``--evalground``
 
  Use evaluator on functions applied to ground arguments.
  
* ``--feelinglucky``
  
  Use evaluator to find counter-examples early.

* ``--unrollcores``
 
  Use unsat-cores to drive unrolling while remaining fair.
  
CVC4 Solver
***********

* ``--solver:cvc4=<cvc4-opt>``
  
  Pass extra command-line arguments to CVC4.

Isabelle
********

* ``--isabelle:base=<path>``

  Specify the installation directory of Isabelle. In Isabelle-parlance, this is
  called ``$ISABELLE_HOME``. It will have the form ``/path/to/Isabelle2015``.
  When no Isabelle installation can be found there, the system suggests to
  enable the ``download`` option.

* ``--isabelle:build``

  Flag to indicate that during the start-up of Leon, Isabelle should
  automatically build all required library sources. This is on by default, and
  should usually be left on. Building only happens when some dependencies
  changed and subsequent runs of Leon don't rebuild the library. However, even
  if nothing is build, it still requires the system a couple of seconds to
  figure that out.

* ``--isabelle:download``

  If necessary, perform a full system bootstrap by downloading and unpacking a
  copy of Isabelle. Off by default. Only supported under Linux.

* ``--isabelle:dump=<path>``

  Makes the system write theory files containing the translated definitions
  and scripts. The generated files may be loaded directly into Isabelle, but
  are not guaranteed to work, as pretty-printing Isabelle terms is only an
  approximation.

* ``--isabelle:mapping``

  Controls function and type mapping. On by default. When switched off, neither
  functions nor types are mapped at all.

* ``--isabelle:strict``

  Strict prover mode. On by default. Replays all referenced proofs from the
  library when verifiying a Leon source file. Keeping it enabled prevents
  unsound proofs when postconditions or mappings in the library are wrong.
  When disabled, a warning is printed.
