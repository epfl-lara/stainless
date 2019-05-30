.. _installation:

Installing Stainless
====================

General Requirement
-------------------

Java 8 JRE. It sufficies to have headless OpenJDK JRE 8 (e.g. one that one gets with ``apt install openjdk-8-jre-headless`` on Debian/Ubuntu). Make sure that ``java -version`` reports a version starting with 1.8, such as ``openjdk version "1.8`` or ``java version "1.8``.


Use Pre-Packaged JAR file
-------------------------

1. Download the latest Stainless JAR from the `Releases page on GitHub <https://github.com/epfl-lara/stainless/releases>`_

2. Paste the following code in a file named ``test.scala``:

.. code-block:: scala

  import stainless.lang._

  object test {
    def ok = {
      assert(true)
    }
  }

3. In a terminal, type the following command, substituting the proper path to the Stainless JAR previously downloaded:

.. code-block:: bash

  $ java -jar /path/to/stainless/jar/file.jar test.scala

4. The output should read:

.. code-block:: text

  [Warning ] The Z3 native interface is not available. Falling back onto princess.
  [  Info  ]  - Checking cache: 'body assertion' VC for ok @5:5...
  [  Info  ] Cache miss: 'body assertion' VC for ok @5:5...
  [  Info  ]  - Now solving 'body assertion' VC for ok @5:5...
  [  Info  ]  - Result for 'body assertion' VC for ok @5:5:
  [  Info  ]  => VALID
  [  Info  ]   ┌───────────────────┐
  [  Info  ] ╔═╡ stainless summary ╞══════════════════════════════════════════════════════════════════════╗
  [  Info  ] ║ └───────────────────┘                                                                      ║
  [  Info  ] ║ ok   body assertion           valid     U:princess      test.scala:5:5           0.931     ║
  [  Info  ] ╟┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄╢
  [  Info  ] ║ total: 1    valid: 1    (0 from cache) invalid: 0    unknown: 0    time:   0.931           ║
  [  Info  ] ╚════════════════════════════════════════════════════════════════════════════════════════════╝
  [  Info  ] Shutting down executor service.

.. _smt-solvers:

External Solver Binaries
------------------------

If no external SMT solvers (such as Z3 or CVC4) are found, Stainless will use the bundled Scala-based `Princess solver <http://www.philipp.ruemmer.org/princess.shtml>`_ 

To improve performance, we highly recommend that you install the following two additional external SMT solvers as binaries for your platform:

* CVC4 1.7, http://cvc4.cs.stanford.edu
* Z3 4.7.1, https://github.com/Z3Prover/z3

You can enable these solvers using ``--solvers=smt-z3`` and ``--solvers=smt-cvc4`` flags.

Solver binaries that you install should match your operating system and your architecture. We recommend that you install these solvers as a binary and have their binaries available in the ``$PATH`` (as ``z3`` or ``cvc4``).

Note that somewhat lower version numbers of solvers should work as well and might even have different sets of soundness-related issues.

You can use multiple solvers in portfolio mode, as with the options ``--timeout=15 --solvers=smt-z3,smt-cvc4``, where verification succeeds if at least one of the solvers proves (within the given number of seconds) each the verification conditions. We suggest to order the solvers starting from the one most likely to succeed quickly.

For final verification runs of highly critical software, we recommend that (instead of the portfolio mode) you obtain several solvers and their versions, then try a single solver at a time and ensure that each verification run succeeds (thus applying N-version programming to SMT solver implementations).

Install Z3 4.7.1 (Linux & macOS)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

1. Download Z3 4.7.1 from https://github.com/Z3Prover/z3/releases/tag/z3-4.7.1
2. Unzip the downloaded archive
3. Copy the ``z3`` binary found in the ``bin/`` directory of the inflated archive to a directory in your ``$PATH``, eg., ``/usr/local/bin``.
4. Make sure ``z3`` can be found, by opening a new terminal window and typing:

.. code-block:: bash

  $ z3 --version

5. The output should read:

.. code-block:: text

  Z3 version 4.7.1 - 64 bit`


Install CVC 1.7 (Linux)
~~~~~~~~~~~~~~~~~~~~~~~

1. Download CVC4 1.7 from http://cvc4.cs.stanford.edu/downloads/builds/x86_64-linux-opt/ (reachable from https://cvc4.github.io/ )

2. Copy or link the downloaded binary under name ``cvc4`` to a directory in your ``$PATH``, eg., ``/usr/local/bin``.

4. Make sure ``cvc4`` can be found, by opening a new terminal window and typing:

.. code-block:: bash

  $ cvc4 --version | head

5. The output should begin with:

.. code-block:: text

  This is CVC4 version 1.7

Install CVC 1.6 (macOS)
~~~~~~~~~~~~~~~~~~~~~~~

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
in an attempt to be more reproducible and independent from sbt cache and path, the instructions below assume that the directory called ``stainless`` does not exist, they instruct ``sbt`` to use a relative path for its bootstrap, and do not require adding ``sbt`` to your path.

**Install sbt**

* Download ``sbt`` 1.2.8, available from http://www.scala-sbt.org/
* Unpack the arhive in some place where you will store them permanently
* Find the path to file ``sbt-launch.jar`` inside the unpacked directory (e.g. under ``sbt/bin/``). Let us call this path ``/path/to/sbt-launch.jar``

**Check out sources**

Get the sources of Stainless by cloning the official Stainless repository:

.. code-block:: bash

  $ git clone https://github.com/epfl-lara/stainless.git
  Cloning into 'stainless'...  

**Run sbt**

The following instructions will invoke sbt while using a stainless sub-directory to download files. 

.. code-block:: bash

  $ cd stainless
  $ java -Dsbt.boot.directory=./sbt-boot/ -jar /path/to/sbt-launch.jar universal:stage

**Where to find generated files**

The compilation will automatically generate the following two bash scripts:

1. ``frontends/scalac/target/universal/stage/bin/stainless-scalac`` that will use the ``scalac`` compiler as frontend,
2. ``frontends/stainless-dotty/target/universal/stage/bin/stainless-dotty`` that uses the ``dotc`` compiler as frontend (experimental).

You may want to introduce a soft-link from ``frontends/scalac/target/universal/stage/bin/stainless-scalac`` to a file called ``stainless``:

.. code-block:: bash

  $ ln -s frontends/scalac/target/universal/stage/bin/stainless-scalac stainless

Analogous scripts work for various platforms and allow additional control over the execution, such as
passing JVM arguments or system properties:

.. code-block:: bash

  $ frontends/scalac/target/universal/stage/bin/stainless-scalac -Dscalaz3.debug.load=true -J-Xmx6G --help

Note that Stainless is organized as a structure of several
projects. The main project lives in ``core`` while the two available
frontends can be found in ``frontends/scalac`` and ``frontends/dotty``.
From a user point of view, this should most of
the time be transparent and the build command should take
care of everything.

Build from Source on Windows 10
-------------------------------

Before following the infrequently updated instructions in this section, considering running Ubuntu on Windows 10  and following the instructions for Linux. That said, Stainless is just a JVM application that invokes binaries that are also available for Windows, so it is not too difficult to build a version that runs without a VM.

Get the sources of Stainless by cloning the official Stainless
repository. You will need a Git shell for windows, e.g. 
`Git for Windows <https://git-for-windows.github.io/>`_.

.. code-block:: bash

  $ git clone https://github.com/epfl-lara/stainless.git
  Cloning into 'stainless'...
  // ...
  $ cd stainless
  $ sbt clean universal:stage
  // takes about 1 minutes
 
Compilation will automatically generate the following two bash scripts:

1. ``frontends/scalac/target/universal/stage/bin/stainless-scalac.bat`` that will use the ``scalac`` compiler as frontend,
2. ``frontends/stainless-dotty/target/universal/stage/bin/stainless-dotty.bat`` that uses the ``dotc`` compiler as frontend (experimental).

Usage within an sbt Project
---------------------------

Setting up an sbt build file to use Stainless is a simple 4-step procedure that avoids the need to explicitly build stainless itself.

1. Start by installing an external solver (see Section ":ref:`smt-solvers`").

2. Add the ``sbt-stainless`` plugin together with the required resolver to your ``project/plugins.sbt``

.. code-block:: scala

  resolvers += Resolver.url(
      "LARA sbt plugins releases",
      url("https://dl.bintray.com/epfl-lara/sbt-plugins/")
    )(Resolver.ivyStylePatterns)

  addSbtPlugin("ch.epfl.lara" % "sbt-stainless" % "<insert-version>")

Check the `sbt-stainless bintray repository <https://bintray.com/epfl-lara/sbt-plugins/sbt-stainless>`_ for the available versions.

3. In your project's build file, enable the ``StainlessPlugin`` on the modules that should be verified by stainless. Below is an example:

.. code-block:: scala

  // build.sbt
  lazy val algorithm = (project in file("algorithm"))
  .enablePlugins(StainlessPlugin) // <-- Enabling stainless verification on this module!
  .settings(...)

Note that if you are using ``.scala`` build files you need to use the fully qualified name ``ch.epfl.lara.sbt.stainless.StainlessPlugin``. Also, because stainless accepts a subset of the Scala language, you may need to refactor your build a bit and code to successfully use stainless on a module.

4. After modifying the build, type ``reload`` if inside the sbt interactive shell. From now on, when executing ``compile`` on a module where the ``StainlessPlugin`` is enabled, stainless will check your Scala code and report errors in the shell (just like any other error that would be reported during compilation).

That's all there is to it. However, the ``sbt-stainless`` plugin is a more recent addition to stainless compared to command-line script. It has seen less testing in the field and currently has the following limitations:

* No incremental compilation support. All sources (included the stainless-library sources) are recompiled at every ``compile`` execution.ub

* The plugin *does not* support Scala 3 (dotty). To track sbt support in dotty you can follow `issue #178 <https://github.com/epfl-lara/stainless/issues/178>`_.

Also, note that the plugin offers a ``stainlessIsEnabled`` setting that can help experimenting with stainless. The ``stainlessIsEnabled`` setting is set to ``true`` by default, but you can flip the flag to false by typing ``set every stainlessIsEnabled := false`` while inside the sbt interactive shell.

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

After installing sphinx, run ``sbt previewSite``. This will generate the documentation and open a browser.

The documentation resides in the ``core/src/sphinx/`` directory and can also be alternatively built without ``sbt``, using the provided ``Makefile``. To do this, in a Linux shell go to the directory ``core/src/sphinx/``,
type ``make html``, and open in your web browser the generated top-level local HTML file, by default stored in 
``src/sphinx/_build/html/index.html``. Also, you can open the ``*.rst`` documentation files in a text editor, as they are human-readable in their source form as well.

