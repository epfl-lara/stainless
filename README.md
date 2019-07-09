Stainless 0.3.1 [![Build Status](http://laraquad4.epfl.ch:9000/epfl-lara/stainless/status/master)](http://laraquad4.epfl.ch:9000/epfl-lara/stainless) [![Gitter chat](https://img.shields.io/gitter/room/gitterHQ/gitter.svg)](https://gitter.im/epfl-lara/stainless)
=============

Verification framework for a subset of the [Scala](http://scala-lang.org) programming language.
Supports contract-driven verification as well as termination checking of higher-order
functional programs with local imperative features (see [Pure Scala](https://epfl-lara.github.io/stainless/purescala.html)
and [Imperative](https://epfl-lara.github.io/stainless/imperative.html)
for more details about the supported fragment).

To get started, see the documentation chapters, such as
  * [Introduction to Stainless](https://epfl-lara.github.io/stainless/intro.html)
  * [Installation](https://epfl-lara.github.io/stainless/installation.html)
  * [Tutorial](https://epfl-lara.github.io/stainless/gettingstarted.html)
  * [Stainless EPFL Page](https://stainless.epfl.ch)
  * [Viktor's keynote at ScalaDays 2017 Copenhagen](https://www.youtube.com/watch?v=d4VeFa0z_Lo)

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
