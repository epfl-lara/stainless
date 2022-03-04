# Stainless [![Release][release-img]][latest-release] [![Nightly Build Status][nightly-larabot-img]][nightly-larabot-ref] [![Build Status][larabot-img]][larabot-ref] [![Gitter chat][gitter-img]][gitter-ref] [![Apache 2.0 License][license-img]][license-ref]

Verification framework for a subset of the [Scala](http://scala-lang.org) programming language.
Supports contract-driven verification as well as termination checking of higher-order
functional programs with local imperative features (see [Pure Scala](https://epfl-lara.github.io/stainless/purescala.html)
and [Imperative](https://epfl-lara.github.io/stainless/imperative.html)
for more details about the supported fragment).
* Stainless Website at EPFL: https://stainless.epfl.ch
* EPFL-LARA Website: https://lara.epfl.ch/w/


## Documentation

To get started, see videos:
  * Tutorials from [EPFL Course](https://lara.epfl.ch/w/fv20/top): [Getting Started](https://tube.switch.ch/videos/c7d203e8),  [Tutorial 1](https://tube.switch.ch/videos/03edee61) [Tutorial 2](https://tube.switch.ch/videos/c22ea3e8) [Tutorial 3](https://tube.switch.ch/videos/7f57f7a9) [Tutorial 4](https://tube.switch.ch/videos/2a9fd35c), [Assertions](https://tube.switch.ch/videos/44e8a0dc), [Unfolding](https://tube.switch.ch/videos/ada8a42c), [Dispenser Example](https://tube.switch.ch/videos/ded227dd)
  * [Viktor's keynote at Lambda Days 2020](https://www.youtube.com/watch?v=dkO59PTcNxA)  
  * [Viktor's keynote at ScalaDays 2017 Copenhagen](https://www.youtube.com/watch?v=d4VeFa0z_Lo)

Tutorials such as one from [FMCAD 2021](https://github.com/epfl-lara/fmcad2021tutorial/), from [ASPLOS 2022](https://epfl-lara.github.io/asplos2022tutorial/) or local documentation chapters, such as:
  * [Documentation](https://epfl-lara.github.io/stainless/)
  * [Introduction to Stainless](https://epfl-lara.github.io/stainless/intro.html)
  * [Installation](https://epfl-lara.github.io/stainless/installation.html)
  * [Getting Started](https://epfl-lara.github.io/stainless/gettingstarted.html)
  * [Command-line Options](https://epfl-lara.github.io/stainless/options.html)
  * [Tutorial](https://epfl-lara.github.io/stainless/tutorial.html)
  * [Stainless EPFL Page](https://stainless.epfl.ch)
  
## Build and Use

To build the project, run `sbt universal:stage`. If all goes well, scripts are generated for Scala 3 and Scala 2 versions of the front end:
  * `frontends/scalac/target/universal/stage/bin/stainless-scalac`
  * `frontends/dotty/target/universal/stage/bin/stainless-dotty`
  
Use one of these scripts as you would use `scalac` to compile Scala files.
The default behavior of Stainless is to formally verify files, instead of generating JVM class files. 
See [frontends/benchmarks/verification/valid/](frontends/benchmarks/verification/valid/) and related directories for some benchmarks and
[bolts repository](https://github.com/epfl-lara/bolts/) for a larger collection.
More information is available in the documentation links.

## License

Stainless is released under the Apache 2.0 license. See the [LICENSE]() file for more information.

---

### Relation to [Inox](https://github.com/epfl-lara/inox)

Stainless relies on Inox to solve the various queries stemming from program verification.
Inox supports model-complete queries in a feature-rich fragment that lets Stainless focus
on program transformations and soundness of both contract and termination checking and uses its own reasoning steps, as well as invocations to solvers (theorem provers) [z3](https://github.com/Z3Prover/z3), [CVC4](https://cvc4.github.io/), and [Princess](http://www.philipp.ruemmer.org/princess.shtml).

[latest-release]: https://github.com/epfl-lara/stainless/releases/latest
[license-img]: https://img.shields.io/badge/license-Apache_2.0-blue.svg?color=134EA2
[license-ref]: https://github.com/epfl-lara/stainless/blob/main/LICENSE
[gitter-img]: https://img.shields.io/gitter/room/gitterHQ/gitter.svg?color=ed1965
[gitter-ref]: https://gitter.im/epfl-lara/stainless
[larabot-img]: http://laraquad4.epfl.ch:9000/epfl-lara/stainless/status/main
[larabot-ref]: http://laraquad4.epfl.ch:9000/epfl-lara/stainless/builds
[nightly-larabot-img]: http://laraquad4.epfl.ch:9000/epfl-lara/stainless/status/main?nightly=true
[nightly-larabot-ref]: http://laraquad4.epfl.ch:9000/epfl-lara/stainless/builds
[release-img]: https://img.shields.io/github/release-pre/epfl-lara/stainless.svg
[tag-date-img]: https://img.shields.io/github/release-date-pre/epfl-lara/stainless.svg?style=popout
