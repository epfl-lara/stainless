# Stainless [![Release][release-img]][latest-release] [![Nightly Build Status][nightly-larabot-img]][nightly-larabot-ref] [![Build Status][larabot-img]][larabot-ref] [![Gitter chat][gitter-img]][gitter-ref] [![Apache 2.0 License][license-img]][license-ref]

Verification framework for a subset of the [Scala](http://scala-lang.org) programming language. See
* [Tutorial (originally for ASPLOS 2022)](https://epfl-lara.github.io/asplos2022tutorial/)
* [EPFL LARA Group Page](https://epfl-lara.github.io/)

## Quick start
[Download the latest `stainless-dotty-standalone` release](https://github.com/epfl-lara/stainless/releases) for your platform.
Unzip the archive, and run Stainless through the `stainless.sh` (or `stainless.bat`) script.
Stainless expects a list of space-separated Scala files to verify.

To check if everything works, you may create a file named `HelloStainless.scala` next to the `stainless.sh` script with the following content:
```scala
import stainless.collection._

object HelloStainless {
  def myTail(xs: List[BigInt]): BigInt = {
    require(xs.nonEmpty)
    xs match {
      case Cons(h, _) => h
      // Match provably exhaustive
    }
  }
}
```

and run `stainless.sh HelloStainless.scala`.
If all goes well, Stainless should report something along the lines:
```
[  Info  ]   ┌───────────────────┐
[  Info  ] ╔═╡ stainless summary ╞════════════════════════════════════════════════════════════════════╗
[  Info  ] ║ └───────────────────┘                                                                    ║
[  Info  ] ║ HelloStainless.scala:6:5:   myTail  body assertion: match exhaustiveness  nativez3   0,0 ║
[  Info  ] ╟┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄╢
[  Info  ] ║ total: 1    valid: 1    (0 from cache) invalid: 0    unknown: 0    time:     0,0         ║
[  Info  ] ╚══════════════════════════════════════════════════════════════════════════════════════════╝
[  Info  ] Shutting down executor service.
```

This archive of Stainless only requires JDK17. In particular, it needs neither a Scala compiler nor SBT.
It is shipped with Z3 4.8.14 and Princess.

## SBT Stainless plugin
Alternatively, one may integrate Stainless with SBT. The supported Scala versions are `3.2.0` and `2.13.6`
To do so, download [sbt-stainless](https://github.com/epfl-lara/stainless/releases), and move it to the directory of the project.
Assuming the project's structure is:
```
MyProject
├── build.sbt
├── project
│   └── build.properties
├── sbt-stainless.zip
└── src/
```

Unzipping `sbt-stainless.zip` should yield the following:
```
MyProject
├── build.sbt
├── project
│   ├── build.properties
│   └── lib                     <--------
│       └── sbt-stainless.jar   <--------
├── sbt-stainless.zip
├── src/
└── stainless/                  <--------
```
That is, it should create a `stainless/` directory and a `lib/` directory with `project/`.
If, instead, the unzipping process creates a `sbt-stainless/` directory containing the `lib/project/` and `stainless/` directories,
these should be moved according to the above structure.

Finally, the plugin must be explicitly enabled for projects in `build.sbt` desiring Stainless with `.enablePlugins(StainlessPlugin)`.
For instance:
```scala
ThisBuild / version := "0.1.0"

ThisBuild / scalaVersion := "3.2.0"

lazy val myTestProject = (project in file("."))
  .enablePlugins(StainlessPlugin) // <--------
  .settings(
    name := "Test"
  )
```

Verification occurs with the usual `compile` command.

Note that this method only ships the Princess SMT solver. Z3 and CVC4 can still be used if their executable can be found in the `$PATH`.

## Build and Use

To start quickly, install a JVM and use a [recent release](https://github.com/epfl-lara/stainless/releases). To build the project, run `sbt universal:stage`. If all goes well, scripts are generated for Scala 3 and Scala 2 versions of the front end:
  * `frontends/scalac/target/universal/stage/bin/stainless-scalac`
  * `frontends/dotty/target/universal/stage/bin/stainless-dotty`

Use one of these scripts as you would use `scalac` to compile Scala files.
The default behavior of Stainless is to formally verify files, instead of generating JVM class files. 
See [frontends/benchmarks/verification/valid/](frontends/benchmarks/verification/valid/) and related directories for some benchmarks and
[bolts repository](https://github.com/epfl-lara/bolts/) for a larger collection.
More information is available in the documentation links.

## Further Documentation and Learning Materials

To get started, see videos:
  * [ASPLOS'22 tutorial](https://epfl-lara.github.io/asplos2022tutorial/)
  * [FMCAD'21 tutorial](https://github.com/epfl-lara/fmcad2021tutorial/)
  * [Formal Verification Course](https://tube.switch.ch/channels/f2d4e01d): [Getting Started](https://tube.switch.ch/videos/c7d203e8),  [Tutorial 1](https://tube.switch.ch/videos/03edee61) [Tutorial 2](https://tube.switch.ch/videos/c22ea3e8) [Tutorial 3](https://tube.switch.ch/videos/7f57f7a9) [Tutorial 4](https://tube.switch.ch/videos/2a9fd35c), [Assertions](https://tube.switch.ch/videos/44e8a0dc), [Unfolding](https://tube.switch.ch/videos/ada8a42c), [Dispenser Example](https://tube.switch.ch/videos/ded227dd)
  * [Keynote at Lambda Days'20](https://www.youtube.com/watch?v=dkO59PTcNxA)  
  * [Keynote at ScalaDays'17 Copenhagen](https://www.youtube.com/watch?v=d4VeFa0z_Lo)

 or see local [documentation](https://epfl-lara.github.io/stainless/) chapters, such as:
  * [Introduction to Stainless](https://epfl-lara.github.io/stainless/intro.html)
  * [Installation](https://epfl-lara.github.io/stainless/installation.html)
  * [Getting Started](https://epfl-lara.github.io/stainless/gettingstarted.html)
  * [Command-line Options](https://epfl-lara.github.io/stainless/options.html)
  * [Mini Tutorial](https://epfl-lara.github.io/stainless/tutorial.html)
  
There is also a [Stainless EPFL Page](https://stainless.epfl.ch).

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
