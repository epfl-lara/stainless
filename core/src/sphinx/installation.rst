.. _installation:

Installing Stainless
====================

Due to its nature, this documentation section may not always
be up to date; we welcome pull requests with carefully
written and tested improvements to the information below.

Use pre-packaged JAR file on Linux & macOS
------------------------------------------

**Requirements:**

* `Java SE Development Kit 8 <http://www.oracle.com/technetwork/java/javase/downloads/jdk8-downloads-2133151.html>`_ or `Java SE Development Kit 7 <http://www.oracle.com/technetwork/java/javase/downloads/jdk7-downloads-1880260.html>`_ for your platform


**Instructions:**

1. Install an external SMT solver (see Section ":ref:`smt-solvers`")

2. Download the latest Stainless JAR from the `Releases page on GitHub <https://github.com/epfl-lara/stainless/releases>`_

3. Paste the following code in a file named ``test.scala``:

.. code-block:: scala

  import stainless.lang._

  object test {
    def ok = {
      assert(true)
    }
  }

4. In a terminal, type the following command, substituting the proper path to the Stainless JAR previously downloaded:

.. code-block:: bash

  $ java -jar /path/to/stainless/jar/file.jar test.scala

5. The output should read:

.. code-block:: text

  [Warning ] The Z3 native interface is not available. Falling back onto smt-z3.
  [  Info  ]  - Checking cache: 'body assertion' VC for ok @5:5...
  [  Info  ] Cache miss: 'body assertion' VC for ok @5:5...
  [  Info  ]  - Now solving 'body assertion' VC for ok @5:5...
  [  Info  ]  - Result for 'body assertion' VC for ok @5:5:
  [  Info  ]  => VALID
  [  Info  ]   ┌───────────────────┐
  [  Info  ] ╔═╡ stainless summary ╞══════════════════════════════════════════════════════════════════════╗
  [  Info  ] ║ └───────────────────┘                                                                      ║
  [  Info  ] ║ ok   body assertion           valid     U:smt-z3        test.scala:5:5           0.931     ║
  [  Info  ] ╟┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄╢
  [  Info  ] ║ total: 1    valid: 1    (0 from cache) invalid: 0    unknown: 0    time:   0.931           ║
  [  Info  ] ╚════════════════════════════════════════════════════════════════════════════════════════════╝
  [  Info  ] Shutting down executor service.

Build from source on Linux & macOS
----------------------------------

**Requirements:**

* `Java SE Development Kit 8 <http://www.oracle.com/technetwork/java/javase/downloads/jdk8-downloads-2133151.html>`_ or `Java SE Development Kit 7 <http://www.oracle.com/technetwork/java/javase/downloads/jdk7-downloads-1880260.html>`_ for your platform
* sbt 0.13.x (Available from http://www.scala-sbt.org/)
* An external SMT solver (see Section ":ref:`smt-solvers`")
* `Sphinx restructured text tool <http://sphinx-doc.org/>`_ (for building local documentation)

**Instructions:**

Get the sources of Stainless by cloning the official Stainless repository:

.. code-block:: bash

  $ git clone https://github.com/epfl-lara/stainless.git
  Cloning into 'stainless'...
  // ...
  $ cd stainless
  $ sbt clean universal:stage
  // takes about 1 minute

The compilation will automatically generate the following two bash scripts:

1. ``frontends/scalac/target/universal/stage/bin/stainless-scalac`` that will use the ``scalac`` compiler as frontend,
2. ``frontends/stainless-dotty/target/universal/stage/bin/stainless-dotty`` that uses the ``dotc`` compiler as frontend (experimental).

You may want to introduce a soft-link from ``frontends/scalac/target/universal/stage/bin/stainless-scalac`` to ``stainless``:

.. code-block:: bash

  $ ln -s frontends/scalac/target/universal/stage/bin/stainless-scalac stainless

These scripts work for all platforms and allow additional control over the execution, such as
passing JVM arguments or system properties:

.. code-block:: bash

  $ frontends/scalac/target/universal/stage/bin/stainless-scalac -Dscalaz3.debug.load=true -J-Xmx6G --help

Note that Stainless is organized as a structure of several
projects. The main project lives in ``core`` while the two available
frontends can be found in ``frontends/scalac`` and ``frontends/dotty``.
From a user point of view, this should most of
the time be transparent and the build command should take
care of everything.

Build from source on Windows
----------------------------

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

Usage within an sbt project
---------------------------

Setting up an sbt build file to use Stainless is a simple 4-step procedure:

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

That's all there is to it. However, the ``sbt-stainless`` plugin currently has the following limitations you should know about:

* No incremental compilation support. All sources (included the stainless-library sources) are recompiled at every ``compile`` execution.

* The plugin only supports vanilla Scala. To track sbt support in dotty you can follow `issue #178 <https://github.com/epfl-lara/stainless/issues/178>`_.

Also, note that the plugin offers a ``stainlessIsEnabled`` setting that can help experimenting with stainless. The ``stainlessIsEnabled`` setting is set to ``true`` by default, but you can flip the flag to false by typing ``set every stainlessIsEnabled := false`` while inside the sbt interactive shell.

.. _smt-solvers:

External Solvers
----------------

`Inox <https://github.com/epfl-lara/inox>`_, the solving backend for Stainless,
relies on SMT solvers for reasoning about quantifier-free formulas.

Inox ships with the JVM SMT solver Princess which should work out of the box on any system, but is quite slow.

It is recommended that you use one of the following external SMT solvers:

* CVC4 1.6, http://cvc4.cs.stanford.edu
* Z3 4.7.1, https://github.com/Z3Prover/z3

Solver binaries that you install should match your operating system and your architecture.
We recommend that you install these solvers as a binary and have their binaries available in the ``$PATH`` (as ``z3`` or ``cvc4``).

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

Install CVC 1.6 (Linux)
~~~~~~~~~~~~~~~~~~~~~~~

1. Download CVC4 1.6 from http://cvc4.cs.stanford.edu/downloads/builds/x86_64-linux-opt/

2. Copy the downloaded binary as ``cvc4`` to a directory in your ``$PATH``, eg., ``/usr/local/bin``.

4. Make sure ``cvc4`` can be found, by opening a new terminal window and typing:

.. code-block:: bash

  $ cvc4 --version

5. The output should begin with:

.. code-block:: text

  This is CVC4 version 1.6

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

To build this documentation locally, you will need Sphinx (
http://sphinx-doc.org/ ), a restructured text toolkit that
was originally developed to support Python documentation.

After installing sphinx, run ``sbt previewSite``. This will generate the documentation and open a browser.

The documentation resides in the ``core/src/sphinx/`` directory and can also be built without ``sbt``
using the provided ``Makefile``. To do this, in a Linux shell go to the directory ``core/src/sphinx/``,
type ``make html``, and open in your web browser the generated top-level local HTML file, by default stored in 
``src/sphinx/_build/html/index.html``. Also, you can open the ``*.rst`` documentation files in a text editor, since
they are human readable in their source form.

Using Stainless in Eclipse
--------------------------

**Untested!**

You first need to tell sbt to globally include the Eclipse plugin in its known plugins.
To do so type 

.. code-block:: bash

 $ echo "addSbtPlugin(\"com.typesafe.sbteclipse\" % \"sbteclipse-plugin\" % \"2.4.0\")" >> ~/.sbt/0.13/plugins/plugins.sbt

In your Stainless home folder, type: ```sbt clean compile eclipse```

This should create all the necessary metadata to load Stainless as a project in Eclipse.

You should now be able to `import the project <http://help.eclipse.org/juno/index.jsp?topic=%2Forg.eclipse.platform.doc.user%2Ftasks%2Ftasks-importproject.htm>`_ into your Eclipse workspace. Don't forget to also import dependencies (the dotty and cafebabe projects, found somewhere in your ~/.sbt directory).

For each run configuration in Eclipse, you have to set the
``ECLIPSE_HOME`` environment variable to point to the home
directory of your Eclipse installation.  To do so, go to 

Run -> Run Configuration 

and then, after picking the configuration you want to run,
set the variable in the Environment tab.

If you want to use ScalaTest from within Eclipse, download the ScalaTest plugin. For instructions, 
see `Using ScalaTest with Eclipse <http://www.scalatest.org/user_guide/using_scalatest_with_eclipse>`_. 
Do NOT declare your test packages as nested packages in
separate lines, because ScalaTest will not see them for some
reason. E.g. don't write

.. code-block:: scala

 package stainless
 package test
 package myTestPackage 

but instead

.. code-block:: scala

 package stainless.test.myTestPackage

