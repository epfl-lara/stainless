Stainless 0.1 [![Build Status](http://laraquad4.epfl.ch:9000/epfl-lara/stainless/status/master)](http://laraquad4.epfl.ch:9000/epfl-lara/stainless)
=============

Verification framework for a subset of the [Scala](http://scala-lang.org) programming language.
Supports contract-driven verification as well as termination checking of higher-order
functional programs with local imperative features (see [Pure Scala](core/src/sphinx/purescala.rst)
and [Imperative](core/src/sphinx/imperative.rst)
for more details about the supported fragment).

To get started, see the documentation chapters, such as
  * [Installation](core/src/sphinx/installation.rst)
  * [Getting Started](core/src/sphinx/gettingstarted.rst)
  * [Introduction to Stainless](core/src/sphinx/intro.rst)

### Relation to [Inox](https://github.com/epfl-lara/inox)

Stainless relies on Inox to solve the various queries stemming from program verification.
Inox supports model-complete queries in a feature-rich fragment that lets Stainless focus
on program transformations and soundness of both contract and termination checking.

### Relation to [Leon](https://github.com/epfl-lara/leon)

The Stainless/Inox stack has grown out of the Leon codebase and subsumes the verification and
termination checking features of Leon. The new projects aim to provide a more stable and
principled implementation of the verification techniques underlying Leon. Feature-wise,
Stainless has already outgrown Leon verification and provides new features such as higher-order
contracts and contract-based termination checking.
