.. _gettingstarted:

Verifying and Compiling Examples
================================

Verifying Examples
------------------

Stainless is currently available as either:

* a command line tool, which exposes most of the functionality, available as a ZIP file or via Docker.
* via a sbt plugin, for use with `Metals <https://scalameta.org/metals/>`_ and your editor of choice, eg. VS Code.

See the :doc:`installation documentation <installation>` for more information.

It is henceforth assumed that there exists a ``stainless`` script in in your ``PATH``.

To see the main options, use

.. code-block:: bash

  $ stainless --help

in your command line shell.
You may also wish to consult the :doc:`available command-line options <options>`.

You can try some of the examples from ``frontends/benchmarks``
distributed with Stainless:

.. code-block:: bash

  $ stainless --solvers=smt-cvc4 frontends/benchmarks/verification/invalid/InsertionSort.scala

and get something like this

.. code-block:: text

  [  Info  ]  - Now solving 'postcondition' VC for buggySortedIns @33:3...
  [  Info  ]  - Result for 'postcondition' VC for buggySortedIns @33:3:
  [  Info  ]  => VALID
  [  Info  ]  - Now solving 'postcondition' VC for buggySortedIns @33:3...
  [  Info  ]  - Result for 'postcondition' VC for buggySortedIns @33:3:
  [Warning ]  => INVALID
  [Warning ] Found counter-example:
  [Warning ]   e: Int  -> -2304
  [Warning ]   l: List -> Cons(-1073744061, Cons(-1073744128, Nil()))
  [  Info  ]  - Now solving 'postcondition' VC for buggySortedIns @33:3...
  [  Info  ]  - Result for 'postcondition' VC for buggySortedIns @33:3:
  [Warning ]  => INVALID
  [Warning ] Found counter-example:
  [Warning ]   e: Int  -> -1084295451
  [Warning ]   l: List -> Cons(1004398524, Cons(-1065353216, Nil()))
  [  Info  ]  - Now solving 'match exhaustiveness' VC for buggySortedIns @35:5...
  [  Info  ]  - Result for 'match exhaustiveness' VC for buggySortedIns @35:5:
  [  Info  ]  => VALID
  [  Info  ]  - Now solving 'postcondition' VC for size @15:3...
  [  Info  ]  - Result for 'postcondition' VC for size @15:3:
  [  Info  ]  => VALID
  [  Info  ]  - Now solving 'postcondition' VC for size @15:3...
  [  Info  ]  - Result for 'postcondition' VC for size @15:3:
  [  Info  ]  => VALID
  [  Info  ]  - Now solving 'match exhaustiveness' VC for size @15:34...
  [  Info  ]  - Result for 'match exhaustiveness' VC for size @15:34:
  [  Info  ]  => VALID
  [  Info  ]  - Now solving 'match exhaustiveness' VC for contents @20:37...
  [  Info  ]  - Result for 'match exhaustiveness' VC for contents @20:37:
  [  Info  ]  => VALID
  [  Info  ]  - Now solving 'match exhaustiveness' VC for isSorted @25:36...
  [  Info  ]  - Result for 'match exhaustiveness' VC for isSorted @25:36:
  [  Info  ]  => VALID
  [  Info  ]   ┌──────────────────────┐
  [  Info  ] ╔═╡ verification summary ╞════════════════════════════════════════════════════════════════════╗
  [  Info  ] ║ └──────────────────────┘                                                                    ║
  [  Info  ] ║ buggySortedIns  postcondition         invalid  U:smt-cvc4  InsertionSort.scala:33:3   0.209 ║
  [  Info  ] ║ buggySortedIns  postcondition         valid    U:smt-cvc4  InsertionSort.scala:33:3   0.358 ║
  [  Info  ] ║ buggySortedIns  postcondition         invalid  U:smt-cvc4  InsertionSort.scala:33:3   0.481 ║
  [  Info  ] ║ buggySortedIns  match exhaustiveness  valid    U:smt-cvc4  InsertionSort.scala:35:5   0.016 ║
  [  Info  ] ║ contents        match exhaustiveness  valid    U:smt-cvc4  InsertionSort.scala:20:37  0.021 ║
  [  Info  ] ║ isSorted        match exhaustiveness  valid    U:smt-cvc4  InsertionSort.scala:25:36  0.035 ║
  [  Info  ] ║ size            postcondition         valid    U:smt-cvc4  InsertionSort.scala:15:3   0.023 ║
  [  Info  ] ║ size            postcondition         valid    U:smt-cvc4  InsertionSort.scala:15:3   0.051 ║
  [  Info  ] ║ size            match exhaustiveness  valid    U:smt-cvc4  InsertionSort.scala:15:34  0.024 ║
  [  Info  ] ╟---------------------------------------------------------------------------------------------╢
  [  Info  ] ║ total: 9    valid: 7    (0 from cache) invalid: 2    unknown: 0    time:   1.218            ║
  [  Info  ] ╚═════════════════════════════════════════════════════════════════════════════════════════════╝


Compiling and Executing Examples
--------------------------------

Scala code written with Stainless library dependencies can be compiled and run using the
library sources available on the `Stainless github repository <https://github.com/epfl-lara/stainless>`_,
and ``scalac`` and ``scala`` 2.12.9.

.. code-block:: bash

  scalac -d /some_folder_for_compiled_classes/ $(find /path/to/stainless/frontends/library/stainless/ -name "*.scala") File1.scala File2.scala ...
  scala -cp /some_folder_for_compiled_classes/ $(find /path/to/stainless/frontends/library/stainless/ -name "*.scala") MainClassName

