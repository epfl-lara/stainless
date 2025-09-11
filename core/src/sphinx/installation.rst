.. _installation:

Installing Stainless
====================

.. _requirements:

General Requirement
-------------------

- Java 17 JRE It suffices to have headless OpenJDK JRE 17 (e.g. one that one
  gets with ``apt install openjdk-17-jre-headless`` on Debian/Ubuntu). Make sure
  that ``java -version`` reports a version starting with 1.17, such as ``openjdk
  version "1.17`` or ``java version "1.17``.

Stainless bundles Scala 3 compiler front-end and runs it before it starts
compilation.

You can obtain Stainless: 

1. via a package manager (see Section :ref:`distribution-install`) 
2. via a standalone release (see Section :ref:`standalone-release`) 
3. by building it from source (see Section :ref:`build-from-source`) 
4. by using it via the SBT plugin (see Section :ref:`sbt-project`)

.. _distribution-install:

Obtain From A Package Manager
-----------------------------

Stainless is available via Snap and the AUR.

Snap
****

A package for Stainless is available on the Snap store as `stainless
<https://snapcraft.io/stainless>`__ with an experimental edge release. It can be
used to install and run Stainless on any Snap enabled system (e.g. Ubuntu).

In a terminal, you can type:

.. code-block:: bash

  $ sudo snap install stainless --edge

This exposes the ``stainless`` command and comes packaged with JDK 17 and z3,
cvc5, and princess as SMT solvers. The edge build follows the latest commit on
the ``main`` branch.

Arch User Repository (AUR)
**************************

A package for Stainless is available on the Arch User Repository (AUR) for
ArchLinux as `stainless-git
<https://aur.archlinux.org/packages/stainless-git>`__, which follows the latest
commit on the ``main`` branch. You can use your favorite AUR helper (we've tried
``yay``, see `AUR Helpers <https://wiki.archlinux.org/title/AUR_helpers>`__), or
follow the `detailed instructions as on the ArchWiki
<https://wiki.archlinux.org/title/Arch_User_Repository#Installing_and_upgrading_packages>`__
to install the package.


For quick reference, with ``yay`` (or other AUR helpers accordingly):

.. code-block:: bash

  $ yay -S stainless-git

and manually:

.. code-block:: bash

  $ git clone https://aur.archlinux.org/stainless-git.git
  $ cd stainless-git
  $ makepkg -si

The option ``-s`` acquires dependencies (``java``, ``git``, ``sbt``) using
``pacman``, and ``-i`` installs Stainless system-wide. Omit ``-i`` to avoid
installing system-wide, and only perform a local build in the directory.

The solver packages ``z3``, ``cvc4``, and ``cvc5``:superscript:`AUR` can be
added as optional dependencies, and having at least one is recommended for
general use.

Issues with the package build should ideally be reported on the `AUR package
page <https://aur.archlinux.org/packages/stainless-git>`__ itself.

.. _github-codespaces:

Github Codespaces
-----------------

To allow running Stainless with only a browser, we have provided a sample
repository to use Stainless with Github Codespaces. Github Codespaces are cloud
machines that can be access via Visual Studio Code locally or in the browser. In
our experience (as of October 2023), this flow works well, given the provided
Ubuntu Linux virtual machines with 16GB of RAM and substantial processing power.
Please see `this repository
<https://github.com/samuelchassot/Stainless-codespaces>`__ for further details.

You can also locally set up Stainless on a self-hosted machine and access it
remotely over SSH with VSCode. 

SSH and VSCode
**************

Visual Studio Code offers a feature allowing to connect to a host over SSH and
edit code located on this host. This is useful to edit code on a remote machine
using the local Visual Studio Code editor and running Stainless on this remote
machine. See `this official documentation
<https://code.visualstudio.com/docs/remote/ssh>`__ to learn more about this
feature.

If you have access to a remote machine over SSH, this is a good way to use
Stainless. Please note that you have to install Stainless on the remote machine
following the instructions above.

.. _standalone-release:

Use Standalone Release 
----------------------

1. Download the latest Stainless release from the `Releases page on GitHub
   <https://github.com/epfl-lara/stainless/releases>`__, under the **Assets**
   section. Make sure to pick the appropriate ZIP for your operating system. The
   releases are bundled with z3 4.12.2+ and cvc5 1.0.8+.

2. Unzip the file you just downloaded to a directory.

3. (Optional) Add this directory to your ``PATH``. This will let you invoke
   Stainless via the ``stainless`` command instead of its fully qualified path
   in step 5.

4. Paste the following code in a file named ``HelloStainless.scala``:

.. code-block:: scala

    import stainless.collection.*

    object HelloStainless {
      def myTail(xs: List[BigInt]): BigInt = {
        require(xs.nonEmpty) 
        xs match
          case Cons(h, _) => h // Match provably exhaustive
      }
    }

5. In a terminal, type the following command, substituting the proper path to
   the directory where you unzipped the latest release:

.. code-block:: bash

  $ /path/to/unzipped/directory/stainless HelloStainless.scala

6. The output should read:

.. code-block:: text

  [  Info  ] Finished compiling                                       
  [  Info  ] Preprocessing finished                                   
  [  Info  ] Finished lowering the symbols                            
  [  Info  ] Finished generating VCs                                  
  [  Info  ] Starting verification...
  [  Info  ]  Verified: 0 / 1
  [  Info  ]  Verified: 1 / 1                     
  [  Info  ] Done in 2.59s
  [  Info  ]   ┌───────────────────┐
  [  Info  ] ╔═╡ stainless summary ╞═════════════════════════════════════════════════════════════════════════════════╗
  [  Info  ] ║ └───────────────────┘                                                                                 ║
  [  Info  ] ║ HelloStainless.scala:6:9:     myTail  body assertion: match exhaustiveness     valid   nativez3   0.1 ║
  [  Info  ] ╟┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄╢
  [  Info  ] ║ total: 1    valid: 1    (0 from cache, 0 trivial) invalid: 0    unknown: 0    time:    0.15           ║
  [  Info  ] ╚═══════════════════════════════════════════════════════════════════════════════════════════════════════╝
  [  Info  ] Verification pipeline summary:
  [  Info  ]   nativez3, non-batched
  [  Info  ] Shutting down executor service.


.. _sbt-project:

Usage Within An Existing Project
--------------------------------

Stainless can also be used within an existing SBT >=1.7.0 project.

1. Start by installing an external solver (see Section ":ref:`smt-solvers`").

2. Download ``sbt-stainless`` from the `GitHub releases
   <https://github.com/epfl-lara/stainless/releases>`__, and move it to the
   directory of the project. Starting from the following project structure:

.. code-block:: text

  MyProject
  ├── build.sbt
  ├── project
  │   └── build.properties
  ├── sbt-stainless.zip
  └── src/

3. Unzipping ``sbt-stainless.zip`` should yield the following:

.. code-block:: text

  MyProject
  ├── build.sbt
  ├── project
  │   ├── build.properties
  │   └── lib                     <--------
  │       └── sbt-stainless.jar   <--------
  ├── sbt-stainless.zip
  ├── src/
  └── stainless/                  <--------

That is, it should create a ``stainless/`` directory and a ``lib/`` directory
with ``project/``. If, instead, the unzipping process creates a
``sbt-stainless/`` directory containing the ``lib/project/`` and ``stainless/``
directories, these should be moved according to the above structure.

4. Finally, the plugin must be explicitly enabled for intended projects in
   ``build.sbt`` with ``.enablePlugins(StainlessPlugin)``. For instance:

.. code-block:: scala

  // build.sbt 
  lazy val algorithm = project
      .in(file("algorithm")) 
      .enablePlugins(StainlessPlugin) // <-- Enabling Stainless verification on this module! 
      .settings(...)

Note that if you are using ``.scala`` build files you need to use the fully
qualified name ``ch.epfl.lara.sbt.stainless.StainlessPlugin``. Also, because
Stainless accepts a subset of the Scala language, you may need to refactor your
build and code somewhat to successfully run Stainless on a module.

5. After modifying the build, type ``reload`` if inside the sbt interactive
   shell. From now on, when executing ``compile`` on a module where the
   ``StainlessPlugin`` is enabled, Stainless will check your Scala code and
   report errors in the shell (just like any other error that would be reported
   during compilation).

That's all there is to it. Note that the ``sbt-stainless`` plugin is a more
recent addition to Stainless compared to command-line script and is still
evolving. For now, there is no incremental compilation support.

Also, note that the plugin offers a ``stainlessEnabled`` setting that can help
in experimenting with Stainless. The ``stainlessEnabled`` setting is set to
``true`` by default, but you can flip the flag to false by typing ``set every
stainlessEnabled := false`` while inside the sbt interactive shell to
temporarily bypass checking.


If you need to run your code with the Stainless SBT plugin, you can create a
``Main.scala`` file as follows in the correct source directory (e.g.
``src/main/scala/your/package/example/Main.scala``):

.. code-block:: scala

  package your.package.example
  
  object Main:
    def main(args: Array[String]): Unit =
      println("Hello, World!")


and then you can run it with:

.. code-block:: bash

  $ sbt "runMain your.package.example.Main"

Note that you `Main` object cannot extend `App` and the `main` function must 
take `args: Array[String]` as parameter.

.. TODO: should we mention more about these dependencies? Given that actors and algebra are not maintained.
.. 6. It is possible to specify extra source dependencies to be added to the set of
..    files processed by Stainless via the ``stainlessExtraDeps`` setting. For
..    example, to add both the ``stainless-algebra`` and ``stainless-actors``
..    packages, along with the latter's dependency on Akka, one can add the
..    following settings to their build:

.. .. code-block:: scala

..    stainlessExtraDeps ++= Seq(
..      "ch.epfl.lara" %% "stainless-algebra" % "0.1.2",
..      "ch.epfl.lara" %% "stainless-actors"  % "0.1.1",
..    )

..    libraryDependencies += "com.typesafe.akka" %% "akka-actor" % "2.5.21"

.. Note that the dependencies specified in ``stainlessExtraDeps`` must be available
.. as a source JAR from any of the resolvers configured in the build.

.. _running-code:

Running Code with Stainless dependencies
----------------------------------------

If you are debugging your scala code before running stainless on it (e.g. using
a simple editor with ``scala-cli --watch``), you can use this workflow with
stainless as well; you just need to make sure that Stainless libraries are
visible to the Scala compiler.

The simplest way is to use the release package, which contains ``stainless-cli``
script, a simple wrapper around ``scala-cli`` that adds the jar dependency on
the compiled and source version of stainless library.

Building a jar:

You can package the Stainless library into a jar like this:

.. code-block:: bash

    $ cd path/to/stainless/ $ sbt stainless-library/packageBin

Add the generated Stainless library jar file when invoking the compiler with
``scalac`` and the JVM with ``scala`` or ``java``. For instance:

.. code-block:: bash

    $ mkdir -p ~/.scala_objects
    $ scalac -d ~/.scala_objects -cp /path/to/stainless/frontends/library/target/scala-3.3.3/stainless-library_3-X.Y.Z-A-BCDEFGHI.jar MyFile1.scala MyFile2.scala # and so on
    $ scala -cp ~/.scala_objects:/path/to/stainless/frontends/library/target/scala-3.3.3/stainless-library_3-X.Y.Z-A-BCDEFGHI.jar MyMainClass

where ``X.Y.Z`` is the Stainless version and ``A-BCDEFGHI`` is some hash (which
can be autocompleted by the terminal).

Using sources:

1. Clone the sources from https://github.com/epfl-lara/stainless

2. Create a folder to put compiled Scala objects: ``mkdir -p ~/.scala_objects``

3. Compile your code (here in ``MyFile.scala``, though you can have more than
   one file) while referring to the Stainless library sources: ``scalac -d
   ~/.scala_objects $(find /path/to/stainless/frontends/library/stainless/ -name
   "*.scala") MyFile.scala``

4. Run your code (replace ``MyMainClass`` with the name of your main object):
   ``scala -cp ~/.scala_objects MyMainClass``


.. _smt-solvers:

External Solver Binaries
------------------------

If no external SMT solvers (such as z3 or cvc5) are found, Stainless will use
the bundled Scala-based `Princess solver
<http://www.philipp.ruemmer.org/princess.shtml>`_

To improve performance, we highly recommend that you install the following two
additional external SMT solvers for your platform:

* cvc5, https://cvc5.github.io/
* z3, https://github.com/Z3Prover/z3

The simplest and recommended way to obtain these solvers is from your package
manager. They are available under their respective names ``z3`` and ``cvc5`` for
Ubuntu, Debian, Fedora, ArchLinux (+ AUR), nixOS, and macOS (via brew), to name
a few. 

You can enable these solvers using ``--solvers=smt-z3`` and
``--solvers=smt-cvc5`` flags. Multiple solvers can be used in portfolio mode, as
with the options ``--timeout=15 --solvers=smt-z3,smt-cvc5``, where verification
succeeds if *at least* one of the solvers proves (within the given number of
seconds) each of the verification conditions. We suggest ordering solvers starting
from the one perceived most likely to succeed quickly.

Note that most recent versions of the solvers should work well and might even
have different sets of soundness-related issues.

For final verification runs of highly critical software, we recommend that
(instead of the portfolio mode) you obtain several solvers and their versions,
then try a single solver at a time and ensure that each verification run
succeeds (thus applying N-version programming to SMT solver implementations).

If needed, the solver binaries are published for various platforms on their
GitHub releases pages. Example installation instructions for chosen versions
follow. They should be similar for other versions and platforms.

Install z3 4.12.2
*****************

1. Download z3 4.12.2 from https://github.com/Z3Prover/z3/releases/tag/z3-4.12.2
2. Unzip the downloaded archive
3. Copy the ``z3`` binary found in the ``bin/`` directory of the inflated
   archive to a directory in your ``$PATH``, eg., ``/usr/local/bin``.
4. Make sure ``z3`` can be found, by opening a new terminal window and typing:

.. code-block:: bash

  $ z3 --version

5. The output should read:

.. code-block:: text

  z3 version 4.12.2 - 64 bit


Install cvc5 1.2.0
******************

1. Download cvc5 1.2.0 from https://github.com/cvc5/cvc5/releases/tag/cvc5-1.2.0
   for your platform. Make sure to pick one of the zip files labeled "static".

2. Unzip the downloaded archive.

3. Copy the ``cvc5`` binary found in the ``bin/`` directory of the inflated
   archive to a directory in your ``$PATH``, eg., ``/usr/local/bin``.

4. Make sure ``cvc5`` can be found, by opening a new terminal window and typing:

.. code-block:: bash

  $ cvc5 --version | head

5. The output should begin with:

.. code-block:: text

  This is cvc5 version 1.0.8

.. _build-from-source:

Build from Source on Linux & macOS
----------------------------------

To build Stainless from source, you need:

1. `Java Development Kit 17 <https://openjdk.org/projects/jdk/17/>`__
2. `sbt 1.6.0+ <https://www.scala-sbt.org>`__
3. `git <https://git-scm.com>`__

For Java and sbt, you can follow their individual installation instructions for
your platform, or use the `standard Scala setup guide here, which uses Coursier
<https://docs.scala-lang.org/getting-started/install-scala.html>`__.

With dependencies in place, you can clone the repository (**recursively**) and
build Stainless:

.. code-block:: bash

  git clone --recursive https://github.com/epfl-lara/stainless
  cd stainless
  sbt Universal/stage

If all goes well, a script is generated for the front end at
``frontends/dotty/target/universal/stage/bin/stainless-dotty``.

It can be useful to introduce a soft-link from this script to a file called
``stainless`` to shorten the reference:

.. code-block:: bash

  $ ln -s frontends/dotty/target/universal/stage/bin/stainless-dotty stainless

Use this script as you would use the Scala compiler ``scalac`` to compile Scala
files. The default behavior of Stainless is to formally verify files, instead of
generating JVM class files.

Analogous scripts work for various platforms and allow additional control over
the execution, such as passing JVM arguments or system properties:

.. code-block:: bash

  $ stainless -Dscalaz3.debug.load=true -J-Xmx6G --help

Note that Stainless is organized as a structure of several projects. The main
project lives in ``core`` while the Scala 3 frontend can be found in
``frontends/dotty``.  From a user's point of view, this should be largely
transparent, and the build command should take care of everything.

Build from Source on Windows
----------------------------

Before following the infrequently updated instructions in this section,
considering running Ubuntu on Windows via `Windows Subsystem for Linux (WSL2)
<https://learn.microsoft.com/en-us/windows/wsl/install>`__ and following the
instructions for Linux.

Get the sources of Stainless by cloning the official Stainless repository. You
will need a Git shell for windows, e.g.  `Git for Windows
<https://git-for-windows.github.io/>`__. On Windows, please do not use ``sbt
Universal/stage`` as this generates a Windows batch file which is unusable,
because it contains commands that are too long for Windows. Instead, please use
``sbt stainless-dotty-standalone/assembly`` as follows:

.. code-block:: bash

  $ git clone --recursive https://github.com/epfl-lara/stainless.git 
  Cloning into 'stainless'... 
  // ... 
  $ cd stainless 
  $ git submodule update --init --recursive 
  $ sbt stainless-dotty-standalone/assembly // takes about 1 minutes

Stainless can then be run with the command: 

.. code-block:: bash

  $ java -jar frontends\stainless-dotty-standalone\target\scala-{SCALA_VERSION}\stainless-dotty-standalone-{VERSION}.jar --help

where ``SCALA_VERSION`` denotes the Scala version and ``VERSION`` denotes
Stainless version and should be replaced with the actual versions. The paths
should be unique, and auto-completion is recommended.

Running Tests
-------------

Stainless comes with a test suite. Use the following commands to invoke
different test suites:

.. code-block:: bash

  $ sbt test 
  $ sbt IntegrationTest/test

It's also possible to run tests in isolation, for example, the following command
runs ``Extraction`` tests on all files in ``termination/looping``:

.. code-block:: bash

  $ sbt 'IntegrationTest/testOnly *ExtractionSuite* -- -z "in termination/looping"'

Building Stainless Documentation
--------------------------------

Stainless documentation is available at https://epfl-lara.github.io/stainless/.
To build the documentation locally, you will need Sphinx
(http://sphinx-doc.org/), a restructured text toolkit that was originally
developed to support Python documentation.

* On Ubuntu 24, you can use ``sudo apt install sphinx-common``

The documentation resides in the ``core/src/sphinx/`` directory and can be built
using the provided ``Makefile``. To do this, in a Linux shell, type ``make
html``, and open in your web browser the generated top-level local HTML file, by
default stored in ``core/src/sphinx/_build/html/index.html``. Also, you can open
the ``*.rst`` documentation files in a text editor, as they are human-readable
in their source form as well.

Note for project maintainers: to build documentation on GitHub Pages, use ``make
gh-pages`` in the same Makefile, or adapt it to your needs.

Using IDEs with --no-colors option. Emacs illustration
------------------------------------------------------

Using command line option ``--no-colors`` asks Stainless to produce clear 7-bit
ASCII output with error messages in a standardized format:

.. code-block:: bash

  FileName.scala:LineNo:ColNo: text of the error message

This helps IDEs to pick up line numbers and show error location in the source
file.

In ``emacs`` editor, you can invoke ``ansi-term`` and
``compilation-shell-minor-mode``. Then, run

.. code-block:: bash

  stainless --no-colors <InputFilesAndOptions>

You may also consider using the ``--watch`` option, which reruns Stainless
and updates the report whenever you save one of the input files.

You should now be able to click on a message for verification condition to jump
to the appropriate position in the appropriate file, as well as to use emacs
commands ``previous-error`` and ``next-error`` to navigate through errors and
other verification-condition outcomes.

Here is a very simple illustration that introduces an interactive
``comp-ansi-term`` command that creates new window with ansi-term and minor
compilation mode:

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

The following globally binds the above command to the F3 key and binds F7 and F8
to commands for navigating reports:

.. code-block:: lisp

  (global-set-key [f3] 'comp-ansi-term)
  (global-set-key [f7] 'previous-error)
  (global-set-key [f8] 'next-error)

For more information, please consult the documentation for ``emacs``.
