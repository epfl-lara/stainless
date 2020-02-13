# Stainless [![Release][release-img]][latest-release] [![Nightly Build Status][nightly-larabot-img]][nightly-larabot-ref] [![Build Status][larabot-img]][larabot-ref] [![Gitter chat][gitter-img]][gitter-ref] [![Apache 2.0 License][license-img]][license-ref]

Verification framework for a subset of the [Scala](http://scala-lang.org) programming language.
Supports contract-driven verification as well as termination checking of higher-order
functional programs with local imperative features (see [Pure Scala](https://epfl-lara.github.io/stainless/purescala.html)
and [Imperative](https://epfl-lara.github.io/stainless/imperative.html)
for more details about the supported fragment).

## Documentation

To get started, see the documentation chapters, such as

  * [Introduction to Stainless](https://epfl-lara.github.io/stainless/intro.html)
  * [Installation](https://epfl-lara.github.io/stainless/installation.html)
  * [Getting Started](https://epfl-lara.github.io/stainless/gettingstarted.html)
  * [Command-line Options](https://epfl-lara.github.io/stainless/options.html)
  * [Tutorial](https://epfl-lara.github.io/stainless/tutorial.html)
  * [Stainless EPFL Page](https://stainless.epfl.ch)
  * [Viktor's keynote at ScalaDays 2017 Copenhagen](https://www.youtube.com/watch?v=d4VeFa0z_Lo)

## Other Links

* Stainless Website: https://stainless.epfl.ch
* EPFL-LARA Website: https://lara.epfl.ch/w/

## License

Stainless is released under the Apache 2.0 license. See the [LICENSE]() file for more information.

---

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

[latest-release]: https://github.com/epfl-lara/stainless/releases/latest
[license-img]: https://img.shields.io/badge/license-Apache_2.0-blue.svg?color=134EA2
[license-ref]: https://github.com/epfl-lara/stainless/blob/master/LICENSE
[gitter-img]: https://img.shields.io/gitter/room/gitterHQ/gitter.svg?color=ed1965
[gitter-ref]: https://gitter.im/epfl-lara/stainless
[larabot-img]: http://laraquad4.epfl.ch:9000/epfl-lara/stainless/status/master
[larabot-ref]: http://laraquad4.epfl.ch:9000/epfl-lara/stainless/builds
[nightly-larabot-img]: http://laraquad4.epfl.ch:9000/epfl-lara/stainless/status/master?nightly=true
[nightly-larabot-ref]: http://laraquad4.epfl.ch:9000/epfl-lara/stainless/builds
[release-img]: https://img.shields.io/github/release-pre/epfl-lara/stainless.svg
[tag-date-img]: https://img.shields.io/github/release-date-pre/epfl-lara/stainless.svg?style=popout

