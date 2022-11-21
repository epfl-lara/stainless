.. _installation:

Installing Stainless
====================

.. _requirements:

General Requirement
-------------------

- Java 17 JRE
  It suffices to have headless OpenJDK JRE 17 (e.g. one that one gets with ``apt install openjdk-17-jre-headless`` on Debian/Ubuntu).
  Make sure that ``java -version`` reports a version starting with 1.17, such as ``openjdk version "1.17`` or ``java version "1.17``.

Stainless bundles Scala compiler front-end and runs it before it starts compilation. We recommend using the Scala 3 front end (originally named dotty), though Scala 2 is also available.

.. _standalone-release:

Use Standalone Release (recommended)
------------------------------------

1. Download the latest Stainless release from the `Releases page on GitHub <https://github.com/epfl-lara/stainless/releases>`_, under the **Assets** section. Make sure to pick the appropriate ZIP for your operating system. This release is bundled with Z3 4.8.14.

2. Unzip the the file you just downloaded to a directory.

3. (Optional) Add this directory to your ``PATH``. This will let you invoke Stainless via the ``stainless`` command instead of its fully qualified path in step 5.

4. Paste the following code in a file named ``HelloStainless.scala``:

.. code-block:: scala

    import stainless.collection._

    object HelloStainless {
      def myTail(xs: List[BigInt]): BigInt = {
        require(xs.nonEmpty)
        xs match {
          case Cons(h, _) => h
          // Match provably exhaustive
        }
      }
    }

5. In a terminal, type the following command, substituting the proper path to the directory where you unzipped the latest release:

.. code-block:: bash

  $ /path/to/unzipped/directory/stainless.sh HelloStainless.scala

6. The output should read:

.. code-block:: text

    [ Debug  ] Generating VCs for functions: myTail
    [ Debug  ] Finished generating VCs
    [  Info  ] Starting verification...
    [  Info  ] Verified: 0 / 1
    [ Debug  ]  - Checking cache: 'body assertion: match exhaustiveness' VC for myTail @6:5...
    [ Debug  ] Cache miss: 'body assertion: match exhaustiveness' VC for myTail @6:5...
    [ Debug  ]  - Now solving 'body assertion: match exhaustiveness' VC for myTail @6:5...
    [ Debug  ]
    [ Debug  ]  - Original VC:
    [ Debug  ]    nonEmpty[BigInt](xs) ==> {
    [ Debug  ]      val scrut: List[BigInt] = xs
    [ Debug  ]      !scrut.isInstanceOf[Cons] ==> false
    [ Debug  ]    }
    [ Debug  ]
    [ Debug  ]  - Simplified VC:
    [ Debug  ]    !nonEmpty[BigInt](xs) || xs.isInstanceOf[Cons]
    [ Debug  ]
    [ Debug  ] Solving with: nativez3
    [ Debug  ]  - Result for 'body assertion: match exhaustiveness' VC for myTail @6:5:
    [ Debug  ]  => VALID
    [  Info  ] Verified: 1 / 1
    [  Info  ]   ┌───────────────────┐
    [  Info  ] ╔═╡ stainless summary ╞═════════════════════════════════════════════════════════════════════════════════╗
    [  Info  ] ║ └───────────────────┘                                                                                 ║
    [  Info  ] ║ HelloStainless.scala:6:5:     myTail  body assertion: match exhaustiveness     valid   nativez3   0,2 ║
    [  Info  ] ╟┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄╢
    [  Info  ] ║ total: 1    valid: 1    (0 from cache, 0 trivial) invalid: 0    unknown: 0    time:    0,17           ║
    [  Info  ] ╚═══════════════════════════════════════════════════════════════════════════════════════════════════════╝
    [  Info  ] Verification pipeline summary:
    [  Info  ]   cache, nativez3
    [  Info  ] Shutting down executor service.

Note: If the warning above says something about falling back on the Princess solver, you might be missing the ``libgomp1`` library,
which you can install with your favorite package manager. For example, on Debian/Ubuntu, just run ``apt-get install libgomp1``.


.. _sbt-project:

Usage Within An Existing Project
********************************

Stainless can also be used within an existing SBT 1.7.x project.

1. Start by installing an external solver (see Section ":ref:`smt-solvers`").

2. Download ``sbt-stainless`` from the `GitHub releases <https://github.com/epfl-lara/stainless/releases>`_, and move it to the directory of the project. You should have the following project structure:

.. code-block::

    MyProject
    ├── build.sbt
    ├── project
    │   └── build.properties
    ├── sbt-stainless.zip       <--------
    └── src/

3. Unzip ``sbt-stainless.zip``:

.. code-block::

    MyProject
    ├── build.sbt
    ├── project
    │   ├── build.properties
    │   └── lib                     <--------
    │       └── sbt-stainless.jar   <--------
    ├── sbt-stainless.zip
    ├── src/
    └── stainless/                  <--------

4. In your project's build file, enable the ``StainlessPlugin`` on the modules that should be verified by Stainless. Below is an example:

.. code-block:: scala

  // build.sbt
  lazy val algorithm = project
    .in(file("algorithm"))
    .enablePlugins(StainlessPlugin) // <-- Enabling Stainless verification on this module!
    .settings(...)

Note that if you are using ``.scala`` build files you need to use the fully qualified name ``ch.epfl.lara.sbt.stainless.StainlessPlugin``. Also, because Stainless accepts a subset of the Scala language, you may need to refactor your build a bit and code to successfully use Stainless on a module.

5. After modifying the build, type ``reload`` if inside the sbt interactive shell. From now on, when executing ``compile`` on a module where the ``StainlessPlugin`` is enabled, Stainless will check your Scala code and report errors in the shell (just like any other error that would be reported during compilation).

That's all there is to it. However, the ``sbt-stainless`` plugin is a more recent addition to Stainless compared to command-line script. Furthermore, there incremental compilation is not supported. All sources (included the stainless-library sources) are recompiled at every ``compile`` execution.ub

Also, note that the plugin offers a ``stainlessEnabled`` setting that can help experimenting with Stainless. The ``stainlessEnabled`` setting is set to ``true`` by default, but you can flip the flag to false by typing ``set every stainlessEnabled := false`` while inside the sbt interactive shell.

6. It is possible to specify extra source dependencies to be added to the set of files processed by Stainless via the ``stainlessExtraDeps`` setting. For example, to add both the ``stainless-algebra`` and ``stainless-actors`` packages, along with the latter's dependency on Akka,
   one can add the following settings to their build:

.. code-block:: scala

   stainlessExtraDeps ++= Seq(
     "ch.epfl.lara" %% "stainless-algebra" % "0.1.2",
     "ch.epfl.lara" %% "stainless-actors"  % "0.1.1",
   )

   libraryDependencies += "com.typesafe.akka" %% "akka-actor" % "2.5.21"

Note that the dependencies specified in ``stainlessExtraDeps`` must be available as a source JAR from any of the resolvers configured in the build.

.. _running-code:

Running Code with Stainless dependencies
----------------------------------------

Using sources:

1. Clone the sources from https://github.com/epfl-lara/stainless

2. Create a folder to put compiled Scala objects: ``mkdir -p ~/.scala_objects``

3. Compile your code (here in ``MyFile.scala``, though you can have more than one file) while referring to the Stainless library sources: ``scalac -d ~/.scala_objects $(find /path/to/Stainless/frontends/library/stainless/ -name "*.scala") MyFile.scala``

4. Run your code (replace ``MyMainClass`` with the name of your main object): ``scala -cp ~/.scala_objects MyMainClass``

Using jar:

You can package the scala library into a jar to avoid the need to compile it every time. For example (for stainless 0.9.6) you can use:

.. code-block:: bash

    $ cd path/to/stainless/
    $ sbt stainless-library/package

Add the generated stainless library jar file when invoking the compiler with `scalac` and the JVM with `scala` or `java`:

.. code-block:: bash

    $ scalac -d ~/.scala_objects -cp /path/to/stainless/frontends/library/target/scala-2.13/stainless-library_2.13-0.9.6.jar MyFile.scala

.. _smt-solvers:

External Solver Binaries
------------------------

If no external SMT solvers (such as Z3 or CVC4) are found, Stainless will use the bundled Scala-based `Princess solver <http://www.philipp.ruemmer.org/princess.shtml>`_

To improve performance, we highly recommend that you install the following two additional external SMT solvers as binaries for your platform:

* CVC4 1.8, http://cvc4.cs.stanford.edu
* Z3 4.8.14, https://github.com/Z3Prover/z3

You can enable these solvers using ``--solvers=smt-z3`` and ``--solvers=smt-cvc4`` flags.

Solver binaries that you install should match your operating system and your architecture. We recommend that you install these solvers as a binary and have their binaries available in the ``$PATH`` (as ``z3`` or ``cvc4``).

Note that somewhat lower version numbers of solvers should work as well and might even have different sets of soundness-related issues.

You can use multiple solvers in portfolio mode, as with the options ``--timeout=15 --solvers=smt-z3,smt-cvc4``, where verification succeeds if at least one of the solvers proves (within the given number of seconds) each the verification conditions. We suggest to order the solvers starting from the one most likely to succeed quickly.

For final verification runs of highly critical software, we recommend that (instead of the portfolio mode) you obtain several solvers and their versions, then try a single solver at a time and ensure that each verification run succeeds (thus applying N-version programming to SMT solver implementations).

Install Z3 4.8.14 (Linux & macOS)
*********************************

1. Download Z3 4.8.14 from https://github.com/Z3Prover/z3/releases/tag/z3-4.8.14
2. Unzip the downloaded archive
3. Copy the ``z3`` binary found in the ``bin/`` directory of the inflated archive to a directory in your ``$PATH``, eg., ``/usr/local/bin``.
4. Make sure ``z3`` can be found, by opening a new terminal window and typing:

.. code-block:: bash

  $ z3 --version

5. The output should read:

.. code-block:: text

  Z3 version 4.8.14 - 64 bit`


Install CVC 1.8 (Linux)
***********************

1. Download CVC4 1.8 from http://cvc4.cs.stanford.edu/downloads/builds/x86_64-linux-opt/ (reachable from https://cvc4.github.io/ )

2. Copy or link the downloaded binary under name ``cvc4`` to a directory in your ``$PATH``, eg., ``/usr/local/bin``.

4. Make sure ``cvc4`` can be found, by opening a new terminal window and typing:

.. code-block:: bash

  $ cvc4 --version | head

5. The output should begin with:

.. code-block:: text

  This is CVC4 version 1.8

Install CVC 1.6 (macOS)
***********************

1. Install `Homebrew <https://brew.sh>`_
2. Install CVC4 using the Homebrew tap at https://github.com/CVC4/homebrew-cvc4
3. Make sure ``cvc4`` can be found, by opening a new terminal window and typing:

.. code-block:: bash

  $ cvc4 --version

4. The output should begin with:

.. code-block:: text

  This is CVC4 version 1.6


Build from Source on Linux & macOS
----------------------------------

To build Stainless, we use ``sbt``. In a typical configuration, ``sbt universal:stage`` in the root of the source tree should work, yet,
in an attempt to be more reproducible and independent from SBT cache and path, the instructions below assume that the directory called ``stainless`` does not exist, they instruct ``sbt`` to use a relative path for its bootstrap, and do not require adding ``sbt`` to your path.

**Install SBT**

Follow the instructions at http://www.scala-sbt.org/ to install ``sbt`` 1.5.6 (or somewhat later version).

**Check out sources**

Get the sources of Stainless by cloning the official Stainless repository:

.. code-block:: bash

  $ git clone https://github.com/epfl-lara/stainless.git
  Cloning into 'stainless'...

**Run SBT**

The following instructions will invoke SBT while using a stainless sub-directory to download files.

.. code-block:: bash

  $ cd stainless
  $ sbt universal:stage

**Where to find generated files**

The compilation will automatically generate the bash script ``stainless-dotty`` (and the Scala2 one ``stainless-scalac``).

You may want to introduce a soft-link from to a file called ``stainless``:

.. code-block:: bash

  $ ln -s frontends/dotty/target/universal/stage/bin/stainless-dotty stainless

and, for the Scala2 version of the front end,

  $ ln -s frontends/scalac/target/universal/stage/bin/stainless-scalac stainless-scalac-old

Analogous scripts work for various platforms and allow additional control over the execution, such as passing JVM arguments or system properties:

.. code-block:: bash

  $ stainless -Dscalaz3.debug.load=true -J-Xmx6G --help

Note that Stainless is organized as a structure of several projects. The main project lives in ``core`` while the two available frontends can be found in ``frontends/dotty`` (and ``frontends/scalac``).  From a user point of view, this should most of the time be transparent and the build command should take care of everything.

Build from Source on Windows 10
-------------------------------

Before following the infrequently updated instructions in this section, considering running Ubuntu on Windows 10 (through e.g. WSL) and following the instructions for Linux.

Get the sources of Stainless by cloning the official Stainless repository. You will need a Git shell for windows, e.g.  `Git for Windows <https://git-for-windows.github.io/>`_.
On Windows, please do not use ``sbt universal:stage`` as this generates a Windows batch file which is unusable, because it contains commands that are too long for Windows.
Instead, please use ``sbt stainless-scalac-standalone/assembly`` as follows:

.. code-block:: bash

  $ git clone https://github.com/epfl-lara/stainless.git
  Cloning into 'stainless'...
  // ...
  $ cd stainless
  $ sbt stainless-scalac-standalone/assembly
  // takes about 1 minutes

Running Stainless can then be done with the command: ``java -jar frontends\stainless-dotty-standalone\target\scala-3.0.2\stainless-dotty-standalone-{VERSION}.jar``, where ``VERSION`` denotes Stainless version.

Running Tests
-------------

Stainless comes with a test suite. Use the following commands to
invoke different test suites:

.. code-block:: bash

  $ sbt test
  $ sbt it:test

It's also possible to run tests in isolation, for example, the following command runs ``Extraction`` tests on all files in ``termination/looping``:

.. code-block:: bash

  $ sbt 'it:testOnly *ExtractionSuite* -- -z "in termination/looping"'

Building Stainless Documentation
--------------------------------

Stainless documentation is available at https://epfl-lara.github.io/stainless/ .
To build the documentation locally, you will need Sphinx (
http://sphinx-doc.org/ ), a restructured text toolkit that
was originally developed to support Python documentation.

* On Ubuntu 18, you can use ``sudo apt install sphinx-common``

The documentation resides in the ``core/src/sphinx/`` directory and can be built using the provided ``Makefile``. To do this, in a Linux shell,
type ``make html``, and open in your web browser the generated top-level local HTML file, by default stored in
``core/src/sphinx/_build/html/index.html``. Also, you can open the ``*.rst`` documentation files in a text editor, as they are human-readable in their source form as well.

Note for project maintainers: to build documentation on GitHub Pages, use ``make gh-pages`` in the same Makefile, or adapt it to you needs.

Using IDEs with --no-colors option. Emacs illustration
------------------------------------------------------

Using command line option ``--no-colors`` asks stainless to produce clear 7-bit ASCII output with error messages in a standardized format:

.. code-block:: bash

  FileName.scala:LineNo:ColNo: text of the error message

This helps IDEs to pick up line numbers and show error location in the source file.

In ``emacs`` editor, you can invoke ``ansi-term`` and ``compilation-shell-minor-mode``. Then, run

.. code-block:: bash

  stainless --no-colors <InputFilesAndOptions>

You may also consider using the ``--watch`` option.

You should now be able to click on a message for verification condition to jump to the appropriate position in the appropriate file, as well as to use emacs commands ``previous-error`` and ``next-error`` to navigate through errors and other verification-condition outcomes.

Here is a very simple illustration that introduces an interactive ``comp-ansi-term`` command that creates new window with ansi-term and minor compilation mode:

.. code-block:: lisp

  (setq comp-terminal-current-number 1)
  (defun create-numbered-comp-terminal ()
    (ansi-term "/bin/bash")
    (rename-buffer (concat "q" (number-to-string comp-terminal-current-number)) 1)
    (setq comp-terminal-current-number (+ comp-terminal-current-number 1))
    (compilation-shell-minor-mode)
  )
  (defun comp-ansi-term (arg)
    "Run ansi-term with bash and compilation-shell-minor-mode in buffer named q_N for increasing N" (interactive "P")
    (create-numbered-comp-terminal)
    (split-window-vertically)
    (previous-buffer)
    (other-window 1)
  )

The following globally binds the above command to the F3 key and binds F7 and F8 to commands for navigating reports:

.. code-block:: lisp

  (global-set-key [f3] 'comp-ansi-term)
  (global-set-key [f7] 'previous-error)
  (global-set-key [f8] 'next-error)

For more information, please consult the documentation for ``emacs``.
