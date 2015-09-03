.. _gettingstarted:

Getting Started
===============

Web Interface
-------------

The simplest way to try out Leon is to use it through the
web interface http://leon.epfl.ch. The web interface uses
standard Javascript and should run in most browsers,
including Chrome and Firefox. 

The web interface requires you to enter your entire program
into the single web editor buffer. For example, you can
paste into the editor the definition of the following `max`
function on unbounded integers:

.. code-block:: scala

  object Max {
    def max(x: BigInt, y: BigInt): BigInt = {
      if (x <= y) y
      else x
    } ensuring(res => x <= res && y <= res)
  }

The above program should verify. If you change `y <= res`
into `y < res`, Leon should report a counterexample; try
clicking on the names of parameters `x` and `y` as well
as various parts in the `ensuring` clause.

You can also **select from a number of provided examples**,
and then edit them subsequently.  Selecting a different
sample program from the web interface will erase the
previously entered program.

The web interface fixes particular settings including the
timeout values for verification and synthesis tasks. For
longer tasks we currently recommend using the command line.

Command Line
------------

Leon can be used as a command line tool, which exposes most
of the functionality. To see the main options, use 

.. code-block:: bash

  ./leon --help

in your command line shell while in the top-level Leon directory.

You can try some of the examples from the `testcases/` directory 
distributed with Leon:

.. code-block:: bash

    $ ./leon --solvers=smt-cvc4 ./testcases/verification/sas2011-testcases/RedBlackTree.scala

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


For more details on how to build Leon from sources that can
be used directly from the shell, see
:ref:`installation`.  In addition to invoking `./leon --help` you
may wish to consult :ref:`cmdlineoptions` options.

Some benchmarks may contain Scala code that is ignored by verifier, but contributes
to running the benchmark. To start a Leon program with Scala, just compile it together
with Leon libraries inside the `library/` directory of Leon distribution. The scripts
`scalacleon` and `scalaleon` attempt to automate this for simple cases and need to be
invoked from the Leon installation directory.
