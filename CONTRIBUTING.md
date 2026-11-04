# Contributing to Stainless

## Getting the sources

Stainless depends on [Inox](https://github.com/epfl-lara/inox), which is included as a git
submodule in `inox/`. Clone recursively, or initialise the submodule in an existing clone:

```bash
git clone --recursive https://github.com/epfl-lara/stainless.git
# or, in an existing clone:
git submodule update --init --recursive
```

Without the submodule, sbt warns that `scalaVersion for subproject inox fell back to a default
value` when loading the build, and compilation fails with
`Error downloading default:inox_3:0.1.0-SNAPSHOT`.

## Stainless cheat sheet

### Keep an sbt server warm

Use `sbtn` (the sbt thin client) instead of `sbt` to keep a background sbt server running between
commands, which avoids reloading the build every time:

```bash
sbtn "stainless-dotty / run /absolute/path/to/file.scala"
sbtn shutdown  # stops the server
```

Note that the server keeps the environment variables and JVM options (`-D...`, `-J...`) it was
started with: commands that depend on them, such as `STAINLESS_UPDATE_EXPECTED` or
`-Dtestsuite-parallelism` below, must be run with `sbt` or after restarting the server.

---

### Debug Stainless (JVM)

---

```bash
sbt -jvm-debug <port>
```

---

### VS Code / Metals Debug Attach

```json
{
  "version": "0.2.0",
  "configurations": [
    {
      "type": "scala",
      "request": "attach",
      "name": "Scala-attach-5005",
      "buildTarget": "root",
      "hostName": "localhost",
      "port": 5005
    }
  ]
}
```

---

### Print the compiler trees that Stainless receives

Stainless' extraction phase (named `stainless`) is scheduled right before `firstTransform`, so it
receives trees after `pickler` and inlining. Stainless forwards unknown options to the compiler,
so the trees can be printed at that exact phase:

```bash
stainless -Vprint:stainless File.scala
```

To print the trees after a phase of a plain Scala compiler, use e.g. `scalac -Vprint:posttyper File.scala`
(`scalac -Vphases` lists the phases).

---

### Run Stainless from sbt (Development)

```bash
sbt
stainless-dotty / run /absolute/path/to/file.scala
```

---

### Run Integration Tests single suite

Example for `stainless.DottyExtractionSuite`

```bash
sbt -batch \
  -Dtestsuite-parallelism=3 \
  -Dtestcase-parallelism=5 \
  "stainless-dotty / IntegrationTest / testOnly stainless.DottyExtractionSuite"
```

---

### Run the GenC golden tests

```bash
sbt -batch "stainless-dotty / IntegrationTest / testOnly stainless.GenCSuite"
```

The GenC benchmarks in `frontends/benchmarks/genc/valid` are verified, translated to C, compared
against the committed `<Name>.expected.c` and `<Name>.expected.h` golden files, and compiled with
`gcc`. The benchmarks with a `<Name>.check` file are also run, and their output (with the lines
concatenated) must match it. To update these files after an intended change, see below.

---

### Update the expected outputs of the tests

Several integration tests compare what they obtain with files of `frontends/benchmarks`:

- `GenCSuite`: the golden C files `<Name>.expected.c` and `<Name>.expected.h`, and the `<Name>.check`
  files with the output of the compiled programs (also checked by `TailRecGenCSuite`);
- `DottyExtractionSuite`: the `.check` files with the errors reported for the programs of
  `extraction/invalid`;
- `VerificationSuite`: the `.check` files listing the VCs of the programs of `verification/invalid`
  (one `position;function;kind;status` line per VC). `<Name>.check` is shared by all the solvers,
  unless a solver has its own `<Name>.check.z3`, `<Name>.check.cvc5` or `<Name>.check.princess`.

When `STAINLESS_UPDATE_EXPECTED=1` is set, these tests write what they obtain to the expected
files that do not match it, instead of failing; the changes are then reviewed with `git diff`:

```bash
STAINLESS_UPDATE_EXPECTED=1 sbt -batch "stainless-dotty / IntegrationTest / testOnly stainless.GenCSuite"
```

The extraction check files and the GenC golden files are created when they are missing. The
optional `.check` files (GenC outputs and VCs) are not: to add one, create it empty and run the
tests in update mode. When several solvers share a VC check file, the first test that checks it
updates it, and the others fail if they obtain different results; the solvers that disagree then
need their own check file.

---

### Run Main of a Stainless project with sbt plugin

This command is used to run the main class of a project verified with stainless when using the stainless sbt plugin.

```bash
runMain your.package.Main
```

---

### Build Stainless sbt Plugin

Run this script to build the sbt plugin

```bash
./bin/package-sbt-plugin.sh
```

---

### Scala → JVM Bytecode Inspection

```bash
scalac File.scala
javap -c -l -private *.class
```

---

### Run Stainless with Explicit JVM Options

```bash
sbt -J-Xmx8G stainless-dotty / run /absolute/path/to/file.scala
```