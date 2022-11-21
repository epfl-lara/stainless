.. _gettingstarted:

Verifying and Compiling Examples
================================

Verifying Examples
------------------

Stainless is currently available as either:

* a command line tool, which exposes most of the functionality, available as a ZIP file (recommended) or via Docker.
* via an SBT plugin.

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

and get something like this (some output cropped)

.. code-block:: text

    [  Info  ] Starting verification...
    [  Info  ] Verified: 3 / 19
    [Warning ]  - Result for 'postcondition' VC for buggySortedIns @37:38:
    [Warning ] l.isInstanceOf[Nil] || !(l.head <= e) || {
    [Warning ]   val res: List = Cons(l.head, buggySortedIns(e, l.tail))
    [Warning ]   assume({
    [Warning ]     val e: List = Cons(l.head, buggySortedIns(e, l.tail))
    [Warning ]     true
    [Warning ]   })
    [Warning ]   contents(res) == contents(l) ++ Set(e) && isSorted(res) && size(res) == size(l) + BigInt("1")
    [Warning ] }
    [Warning ] frontends/benchmarks/verification/invalid/InsertionSort.scala:37:38:  => INVALID
                     case Cons(x,xs) => if (x <= e) Cons(x,buggySortedIns(e, xs)) else Cons(e, l)
                                                    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
    [Warning ] Found counter-example:
    [Warning ]   l: List -> Cons(-770374653, Cons(-771685886, Nil()))
    [Warning ]   e: Int  -> 1376322050
    [  Info  ] Verified: 3 / 19
    [Warning ]  - Result for 'postcondition' VC for buggySortedIns @37:73:
    [Warning ] l.isInstanceOf[Nil] || l.head <= e || {
    [Warning ]   val res: List = Cons(e, l)
    [Warning ]   contents(res) == contents(l) ++ Set(e) && isSorted(res) && size(res) == size(l) + BigInt("1")
    [Warning ] }
    [Warning ] frontends/benchmarks/verification/invalid/InsertionSort.scala:37:73:  => INVALID
                     case Cons(x,xs) => if (x <= e) Cons(x,buggySortedIns(e, xs)) else Cons(e, l)
                                                                                       ^^^^^^^^^^
    [Warning ] Found counter-example:
    [Warning ]   l: List -> Cons(691483681, Cons(512, Nil()))
    [Warning ]   e: Int  -> -1263292350
    [  Info  ] Verified: 17 / 19
    [  Info  ]   ┌───────────────────┐
    [  Info  ] ╔═╡ stainless summary ╞══════════════════════════════════════════════════════════════════════════════════════════════╗
    [  Info  ] ║ └───────────────────┘                                                                                              ║
    [  Info  ] ║ InsertionSort.scala:33:7:    buggySortedIns  non-negative measure                  valid             U:smt-z3  0,1 ║
    [  Info  ] ║ InsertionSort.scala:35:5:    buggySortedIns  body assertion: match exhaustiveness  trivial                     0,0 ║
    [  Info  ] ║ InsertionSort.scala:35:5:    buggySortedIns  postcondition                         trivial                     0,0 ║
    [  Info  ] ║ InsertionSort.scala:36:21:   buggySortedIns  postcondition                         valid             U:smt-z3  0,1 ║
    [  Info  ] ║ InsertionSort.scala:37:38:   buggySortedIns  postcondition                         invalid           U:smt-z3  0,3 ║
    [  Info  ] ║ InsertionSort.scala:37:45:   buggySortedIns  measure decreases                     valid             U:smt-z3  0,1 ║
    [  Info  ] ║ InsertionSort.scala:37:73:   buggySortedIns  postcondition                         invalid           U:smt-z3  0,1 ║
    [  Info  ] ║ InsertionSort.scala:20:7:    contents        non-negative measure                  valid from cache            0,0 ║
    [  Info  ] ║ InsertionSort.scala:20:37:   contents        body assertion: match exhaustiveness  trivial                     0,0 ║
    [  Info  ] ║ InsertionSort.scala:22:24:   contents        measure decreases                     valid             U:smt-z3  0,0 ║
    [  Info  ] ║ InsertionSort.scala:25:7:    isSorted        non-negative measure                  valid             U:smt-z3  0,0 ║
    [  Info  ] ║ InsertionSort.scala:25:36:   isSorted        body assertion: match exhaustiveness  trivial                     0,0 ║
    [  Info  ] ║ InsertionSort.scala:28:44:   isSorted        measure decreases                     valid             U:smt-z3  0,1 ║
    [  Info  ] ║ InsertionSort.scala:15:7:    size            non-negative measure                  valid from cache            0,0 ║
    [  Info  ] ║ InsertionSort.scala:15:34:   size            body assertion: match exhaustiveness  trivial                     0,0 ║
    [  Info  ] ║ InsertionSort.scala:15:34:   size            postcondition                         trivial                     0,0 ║
    [  Info  ] ║ InsertionSort.scala:16:19:   size            postcondition                         valid             U:smt-z3  0,0 ║
    [  Info  ] ║ InsertionSort.scala:17:25:   size            postcondition                         valid             U:smt-z3  0,0 ║
    [  Info  ] ║ InsertionSort.scala:17:29:   size            measure decreases                     valid from cache            0,0 ║
    [  Info  ] ╟┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄╢
    [  Info  ] ║ total: 19   valid: 17   (3 from cache, 6 trivial) invalid: 2    unknown: 0    time:    0,81                        ║
    [  Info  ] ╚════════════════════════════════════════════════════════════════════════════════════════════════════════════════════╝
    [  Info  ] Verification pipeline summary:
    [  Info  ]   cache, anti-aliasing, smt-z3
    [  Info  ] Shutting down executor service.


Compiling and Executing Examples
--------------------------------

Scala code written with Stainless library dependencies can be compiled and run using the
library sources available on the `Stainless github repository <https://github.com/epfl-lara/stainless>`_,
along with the scala compiler and runner script.

.. code-block:: bash

  scalac -d /some_folder_for_compiled_classes/ $(find /path/to/stainless/frontends/library/stainless/ -name "*.scala") File1.scala File2.scala ...
  scala -cp /some_folder_for_compiled_classes/ $(find /path/to/stainless/frontends/library/stainless/ -name "*.scala") MainClassName
