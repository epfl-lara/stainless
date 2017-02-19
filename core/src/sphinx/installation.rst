.. _installation:

Installing Stainless
====================

Stainless is probably easiest to build on Linux-like
platforms, but read on regarding other platforms.

Due to its nature, this documentation section may not always
be up to date; we welcome pull requests with carefully
written and tested improvements to the information below.

**Requirements:**

* `Java SE Development Kit 8 <http://www.oracle.com/technetwork/java/javase/downloads/jdk8-downloads-2133151.html>`_ or `Java SE Development Kit 7 <http://www.oracle.com/technetwork/java/javase/downloads/jdk7-downloads-1880260.html>`_ for your platform
* SBT 0.13.x (Available from http://www.scala-sbt.org/)
* `Sphinx restructured text tool <http://sphinx-doc.org/>`_ (for building local documentation)

Linux & Mac OS-X
----------------

Get the sources of Stainless by cloning the official Stainless repository:

.. code-block:: bash

  $ git clone https://github.com/epfl-lara/stainless.git
  Cloning into 'stainless'...
  // ...
  $ cd stainless
  $ sbt clean compile
  // takes about 1 minute

Compilation will automatically generate the following two bash scripts:
1. ``bin/stainless-scalac`` that will use the ``scalac`` compiler as frontend,
2. ``bin/stainless-dotty`` that uses the ``dotc`` compiler as frontend (experimental).

You may want to introduce a soft-link from ``bin/stainless-scalac`` to ``stainless``:

.. code-block:: bash

  $ ln -s bin/stainless-scalac stainless

Note that Stainless is organized as a structure of several
projects. The main project lives in ``core`` while the two available
frontends can be found in ``frontends/scalac`` and ``frontends/dotty``.
From a user point of view, this should most of
the time be transparent and the build command should take
care of everything.

Windows
-------

Get the sources of Stainless by cloning the official Stainless
repository. You will need a Git shell for windows, e.g. 
`Git for Windows <https://git-for-windows.github.io/>`_.

.. code-block:: bash

  $ git clone https://github.com/epfl-lara/stainless.git
  Cloning into 'stainless'...
  // ...
  $ cd stainless
  $ sbt clean compile
  // takes about 1 minutes
 
Compilation will automatically generate the following two bash scripts:
1. ``bin/stainless-scalac`` that will use the ``scalac`` compiler as frontend,
2. ``bin/stainless-dotty`` that uses the ``dotc`` compiler as frontend (experimental).

You will now need to either port the bash scripts to Windows, or to run them
under Cygwin.

.. _smt-solvers:

External Solvers
----------------

`Inox <https://github.com/epfl-lara/inox>`_, the solving backend for Stainless,
relies on SMT solvers for reasoning about quantifier-free formulas.
See `inox' solver documentation <https://github.com/epfl-lara/inox#solver-backends>`_
for more information on how to get/install these solvers.

Note that for the `Native Z3 API <https://github.com/epfl-lara/inox#native-z3-api>`_
to be available, you will have to place the jar produced by building
`ScalaZ3 <https://github.com/epfl-lara/ScalaZ3>`_ into
``unmanaged/scalaz3-$os-$arch-$scalaVersion.jar``.

Running Tests
-------------

Stainless comes with a test suite. Consider running the following commands to
invoke different test suites:

.. code-block:: bash

  $ sbt test
  $ sbt it:test

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
see `Using ScalaTest with Eclise <http://www.scalatest.org/user_guide/using_scalatest_with_eclipse>`_. 
Do NOT declare your test packages as nested packages in
separate lines, because ScalaTest will not see them for some
reason. E.g. don't write

.. code-block:: scala

 package leon
 package test
 package myTestPackage 

but instead

.. code-block:: scala

 package leon.test.myTestPackage

