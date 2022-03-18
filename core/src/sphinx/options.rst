.. _cmdlineoptions:

Specifying Options
==================

Stainless's command line options have the form ``--option`` or ``--option=value``.
To enable a flag option, use ``--option=true`` or ``on`` or ``yes``,
or just ``--option``. To disable a flag option, use ``--option=false``.

Additionally, if you need to pass options to the ``scalac`` frontend of Stainless,
you can do it by using a single dash ``-``. For example, try ``-Ybrowse:typer``.

The rest of this section presents some of the command-line options that Stainless recognizes.
For a short (but always up-to-date) summary, you can also invoke ``stainless --help``.

Choosing which Stainless feature to use
---------------------------------------

The first group of options determines which feature of Stainless will be used.
By default, ``--verification`` is chosen.

* ``--verification``

  Proves or disproves function contracts, as explained in the :doc:`verification` section.

* ``--eval``

  Evaluate parameterless functions and report their body's value and whether
  or not their postcondition holds.

* ``--genc``

  Convert stainless code to C (implies --batched, default: false).
  See documentation section for generating C code.

* ``--coq``

  Transform the program into a Coq program, and let Coq generate subgoals automatically

* ``--type-checker``

  Use type checker inspired by System FR to generate verification conditions.
  Default is ``true`` and is strongly recommended; using ``false`` reverts to
  an old verification-condition generator.

* ``--infer-measures=[yes|no|only] (default: yes)``

  Infers measures for recursive functions which do not already have one.

* ``--check-measures=[true|false] (default: true)``

  Check termination of functions with measures, ie. whether measures decrease between recursive calls.

* ``--testgen``

  Proves or disproves function contracts (like ``--verification``) and attempts to create Scala test cases from reported counter-examples.

* ``--genc-testgen``

  Like ``--testgen``, but generates C test cases using GenC.

* ``--help``

  Prints a helpful message, then exits.


Additional top-level options
----------------------------

These options are available to all Stainless components:

* ``--watch``

  Re-run the selected analysis components upon file changes, making the program analysis
  interactive and significantly more efficient than restarting stainless manually.

* ``--no-colors``

  Disable colored output and non-ascii characters (consider this option for better support in IDEs)

* ``--compact``

  Reduces the components' summaries to only the invalid elements (e.g. invalid VC).

* ``--debug=d1,d2,...``

  Enables printing detailed messages for the components d1,d2,... .
  Available components include:

  * ``solver`` (SMT solvers and their wrappers)

  * ``termination`` (Termination analysis)

  * ``timers`` (Timers, timer pools)

  * ``trees`` (Manipulation of trees)

  * ``verification`` (Verification)

  * ``full-vc`` (Display VCs before and after simplification)

  * ``type-checker`` (Type checking of the final program for VC generation)

  * ``type-checker-vcs`` (Generation of VCs by the type-checker)

  * ``derivation`` (Dump typing derivations)

* ``--functions=f1,f2,...``

  Only consider functions f1, f2, ... . This applies to all functionalities
  where Stainless manipulates the input in a per-function basis.

  Stainless will match against suffixes of qualified names. For instance:
  ``--functions=List.size`` will match the method ``stainless.collection.List.size``,
  while  ``--functions=size`` will match all methods and functions named ``size``.
  This option supports ``_`` as wildcard: ``--functions=List._`` will
  match all ``List`` methods.

* ``--solvers=s1,s2,...``

  Use solvers s1, s2,... . If more than one solver is chosen, all chosen
  solvers will be used in parallel, and the best result will be presented.
  By default, the ``nativez3`` solver is picked.

  Some solvers are specialized in proving verification conditions
  and will have a hard time finding a counterexample in the case of an invalid
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
    unfolding. This is a full-stack JVM solver and enables Stainless to run without
    external solver dependencies.

* ``--timeout=t``

  Set a timeout for each attempt to prove one verification condition/
  repair one function (in sec.) When using the ``--eval`` component, one
  should use ``--max-calls`` instead.

* ``--cache``

  Use persistent cache on disk to save the state of the verification and/or
  termination analyses.

* ``--cache-dir=<directory>``

  Specify in which directory the cache files generated by ``--cache`` and other
  options should be stored. Defaults to ``.stainless-cache/``.

* ``--json=<file>``

  Export the verification and/or termination analyses to the given file.

* ``--extra-deps=org:name_scalaVersion:version,...``

  Fetch the specified dependencies, and add their sources to the set of files
  processed by Stainless. Each dependency must be available as a source JAR
  from MavenCentral, the EPFL-LARA bintray organization, your local Ivy database,
  or through another resolver specified via ``--extra-resolvers``.

  Note: Stainless will not pull transitive dependencies, so one has to specify
  all transitive dependencies explicitely via this option.

  Example: ``--extra-deps=ch.epfl.lara:stainless-algebra_2.12:0.1.2``

* ``--extra-resolvers=URL,...``

  Specify additional resolvers to be used to fetch the dependencies specified via
  the ``--extra-deps`` option.

  Note: The full URL of the resolver must be used.

  Example: ``--extra-resolvers=https://oss.sonatype.org/content/repositories/snapshots/``

  See the `Coursier source code <https://github.com/coursier/coursier/blob/8d011f7eeb2a9dde5ed2518fb2407e7aaecfc54f/modules/coursier/shared/src/main/scala/coursier/Repositories.scala>`_ for the list of most common repositories URLs.


Additional Options (by component)
---------------------------------

The following options relate to specific components in Stainless.


Verification
************

* ``--strict-aritmetic``

  Check arithmetic operations for unintended behaviour and
  overflows.  Note that reasoning about bitvectors is sound
  even if this option is false, but in that case no warnings
  are generated for overflows and underflows because these
  have well-defined semantics in Scala.

* ``--vc-cache``

  Use a persistent cache mechanism to speed up verification; on by default.

* ``--fail-early``

  Aborts verification as soon as a VC cannot be proven to be correct.

* ``--fail-invalid``

  Aborts verification as soon as an invalid VC is found.



Termination
***********

* ``--ignore-posts``

  Ignore postconditions during termination verification.



Unrolling Solver
****************

* ``--check-models``

  Double-check counterexamples with the evaluator.

* ``--feeling-lucky``

  Use evaluator to find counterexamples early.

* ``--unroll-assumptions``

  Use unsat-assumptions to drive unrolling while remaining fair.

* ``--silent-errors``

  Don't crash on errors, simply return ``Unknown``.

* ``--unroll-factor=n``

  Speeds up unrolling by a factor ``n``.

* ``--model-finding=n``

  Boosts model-finding capabilities by a factor ``n``. This may come at
  the cost of proof construction.

* ``--no-simplifications``

  Disables program simplification heuristics.



CVC4 Solver
***********

* ``--solver:cvc4=<cvc4-opt>``

  Pass extra command-line arguments to CVC4.



Evaluators
**********

* ``--codegen``

  Use compiled evaluator instead of an interpreter.

* ``--small-arrays``

  Assume all arrays can fit into memory during compiled evaluation.

* ``--instrument``

  Instrument ADT field access during code generation.

* ``--max-calls=n``

  Bounds the total number of function call evaluations (before crashing).

* ``--ignore-contracts``

  Ignores function contracts during evaluation.



Tests generation
****************

* ``testgen-file=<file>``

  Specifies the output file for the generated tests.

* ``genc-testgen-includes=header1.h,header2,...``

  Only applies for ``--genc-testgen``. Indicates the headers to ``#include`` in the generated test file.

Configuration File
------------------

Stainless supports setting default values for command line options configuration files.
To specify configuration file you can use the option ```--config-file=FILE``. The default is
``stainless.conf`` or ``.stainless.conf``. The file should be a valid HOCON file.

For example, consider the config file containin the following lines:

.. code-block:: text

   vc-cache = false
   debug = [verification, trees]
   timeout = 5
   check-models = true
   print-ids = true


The file will translate to the following command line options:

``--vc-cache=false --debug=verification,trees --timeout=5 --print-ids``

Stainless searches for a configuration file recursively
starting from the current directory and walking up the
directory hierarchy.  For example, if one runs stainless
from ``/a/b/c`` and there is a config file in any of `c`,
`b` or `a`, the first of those is going to be loaded.

Library Files
-------------

Purpose of library files
************************

Stainless contains library source Scala files that define types and functions that are meant to be always available
via import statements such as ``import stainless.lang._``, ``import stainless.annotation._``,
``import stainless.collection._``, and so on. Many of these types have special treatment inside the extraction
pipeline and will map directly to mathematical data types of the underlying SMT solvers.
At build time, the ``build.sbt`` script computes the list of these files by traversing the ``frontends/library/`` directory.

Changing the list of library files
**********************************

To support further customization, if at run time stainless finds
a file ``libfiles.txt`` in the current directory, it replaces the list of library files files with the list contained
in this file, one file per line, with paths relative to the directory ``frontends/library/``. For example, ``libfiles.txt``
may contain:

.. code:: text

   stainless/util/Random.scala
   stainless/lang/Option.scala
   stainless/lang/StaticChecks.scala
   stainless/lang/Real.scala
   stainless/lang/Either.scala
   stainless/lang/Set.scala
   stainless/lang/MutableMap.scala
   stainless/lang/package.scala
   stainless/lang/Bag.scala
   stainless/lang/Map.scala
   stainless/collection/List.scala
   stainless/math/BitVectors.scala
   stainless/math/Nat.scala
   stainless/math/package.scala
   stainless/io/StdIn.scala
   stainless/io/package.scala
   stainless/annotation/annotations.scala
   stainless/annotation/isabelle.scala
   stainless/annotation/cCode.scala
   stainless/proof/Internal.scala
   stainless/proof/package.scala

Shortening this list may reduce the startup time, but also cause Stainless to not work propertly, so
using the ``--watch`` and ``--functions`` options is the first option to try.

For further customization by advanced users, please examine the ``build.sbt`` file.
