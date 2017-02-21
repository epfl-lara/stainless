.. _gettingstarted:

Getting Started
===============

Stainless is currently only available as a command line tool,
which exposes most of the functionality. See the
`installation documentation <installation.rst>`_
for more information.

Stainless compilation will generate two scripts for you, namely
``bin/stainless-scalac`` and ``bin/stainless-dotty``. The dotty
frontend is experimental for now so lets start by introducing
a soft-link from ``bin/stainless-scalac`` to ``stainless``

.. code-block:: bash

  $ ln -s bin/stainless-scalac stainless

To see the main options, use

.. code-block:: bash

  $ ./stainless --help

in your command line shell while in the top-level Stainless directory.
You may also wish to consult the `available command-line options <options.rst>`_.

You can try some of the examples from ``fontends/scalac/src/it/resources/regression/``
distributed with Stainless:

.. code-block:: bash

  $ ./stainless --solvers=smt-cvc4 frontends/scalac/src/it/resources/regression/verification/invalid/RedBlackTree.scala

and get something like this

.. code-block:: bash

   ┌──────────────────────┐
 ╔═╡ Verification Summary ╞═══════════════════════════════════════════════════════════════════╗
 ║ └──────────────────────┘                                                                   ║
 ║ add                          postcondition          82:15   valid    U:smt-cvc4      0.258 ║
 ║ add                          precondition           81:15   valid    U:smt-cvc4      0.007 ║
 ║ add                          precondition           81:5    valid    U:smt-cvc4      0.049 ║
 ║ balance                      match exhaustiveness   90:5    valid    U:smt-cvc4      0.006 ║
 ║ balance                      postcondition          101:15  valid    U:smt-cvc4      0.301 ║
 ║ blackBalanced                match exhaustiveness   45:43   valid    U:smt-cvc4      0.006 ║
 ║ blackHeight                  match exhaustiveness   50:40   valid    U:smt-cvc4      0.009 ║
 ║ buggyAdd                     postcondition          87:15   invalid  U:smt-cvc4      1.561 ║
 ║ buggyAdd                     precondition           86:5    invalid  U:smt-cvc4      0.135 ║
 ║ buggyBalance                 match exhaustiveness   104:5   invalid  U:smt-cvc4      0.008 ║
 ║ buggyBalance                 postcondition          115:15  invalid  U:smt-cvc4      0.211 ║
 ║ content                      match exhaustiveness   17:37   valid    U:smt-cvc4      0.030 ║
 ║ ins                          match exhaustiveness   59:5    valid    U:smt-cvc4      0.007 ║
 ║ ins                          postcondition          66:15   valid    U:smt-cvc4      3.996 ║
 ║ ins                          precondition           62:37   valid    U:smt-cvc4      0.034 ║
 ║ ins                          precondition           64:40   valid    U:smt-cvc4      0.036 ║
 ║ makeBlack                    postcondition          77:14   valid    U:smt-cvc4      0.036 ║
 ║ redDescHaveBlackChildren     match exhaustiveness   40:53   valid    U:smt-cvc4      0.005 ║
 ║ redNodesHaveBlackChildren    match exhaustiveness   34:54   valid    U:smt-cvc4      0.007 ║
 ║ size                         match exhaustiveness   22:33   valid    U:smt-cvc4      0.005 ║
 ║ size                         postcondition          25:15   valid    U:smt-cvc4      0.055 ║
 ╟┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄╢
 ║ total: 21     valid: 17     invalid: 4      unknown 0                                6.762 ║
 ╚════════════════════════════════════════════════════════════════════════════════════════════╝

