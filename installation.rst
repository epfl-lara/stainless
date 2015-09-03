.. _installation:

Installing Leon
===============

Leon requires quite a few dependencies, and you will need to make sure
everything is correctly set up before being able to build it. Leon is probably
much easier to build on Unix-like platforms. Not to say it is impossible to
build on Windows. But some scripts used to run and test the system are shell
script and you will need to manually port them to Windows if you wish to use
Windows.


**Requirements:**

* `1.7  Java Development Kit <http://www.oracle.com/technetwork/java/javase/downloads/jdk7-downloads-1880260.html>`_

* SBT 0.13.X (Available from http://www.scala-sbt.org/)

* Support for at least one SMT solver (See :ref:`smt-solvers`)

Linux & Mac OS-X
----------------

Get the sources of Leon by cloning the official Leon repository:

.. code-block:: bash

 $ git clone https://github.com/epfl-lara/leon.git
 Cloning into 'leon'...
 // ...
 $ cd leon
 $ sbt clean compile
 // takes about 3 minutes
 
We now use ``sbt script`` to create a ``leon`` bash script that runs Leon with
all the appropriate settings:

.. code-block:: bash
 
 $ sbt script
 $ ./leon --help


Windows
-------

Get the sources of Leon by cloning the official Leon repository (You will need a git shell for windows e.g. https://msysgit.github.io/):

.. code-block:: bash

 $ git clone https://github.com/epfl-lara/leon.git
 Cloning into 'leon'...
 // ...
 $ cd leon
 $ sbt clean compile
 // takes about 3 minutes
 
We now use ``sbt script`` to create a ``leon`` bash script that runs leon with
all the appropriate settings:

.. code-block:: bash
 
 $ sbt script

You will now need to either port the bash script to Windows, or to run it
under Cygwin.

**Known issues**

*Missing jars*

If running leon produces errors because it could not find some cafebabe*.jar or vanuatoo*.jar, it is probably because symlinks have not been resolved. If your architecture is x64, do the following:

1. Copy unmanaged/common/cafebabe*.jar to unmanaged/64/
2. Copy unmanaged/common/vanuatoo*.jar to unmanaged/64/

.. _smt-solvers:

SMT Solvers
-----------

Leon relies on SMT solvers to solve the constraints it generates. We currently
support two major SMT solvers: 

  * CVC4, http://cvc4.cs.nyu.edu/web/
  * Z3, https://github.com/Z3Prover/z3

For Linux users, a native Z3 API is bundled with Leon and should work out of the
box. For OS-X and Windows users, you will either have to recompile the native
communication layer yourself or use the SMT-LIB API.

Solver binaries that you install should match your operating system and
your architecture.

In any case, we recommend that you install both solvers separately and have
their binaries available in the ``$PATH``.

Since the default solver uses the native Z3 API, you will have to explicitly
specify another solver if this native layer is not available to you. Check also 
the ``--solvers`` option in :ref:`cmdlineoptions` .

Building Documentation
----------------------

To build this documentation locally, you will need Sphinx (
http://sphinx-doc.org/ ), a restructured text toolkit that
was originally developed to support Python documentation.

After installing sphinx, run ``sbt previewSite``. This will generate the documentation and open a browser.
