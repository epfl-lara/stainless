# Stainless [![Release][release-img]][latest-release] [![Nightly Status](https://github.com/epfl-lara/stainless/actions/workflows/stainless-nightly.yml/badge.svg)](https://github.com/epfl-lara/stainless/actions/workflows/stainless-nightly.yml) [![Build Status](https://github.com/epfl-lara/stainless/actions/workflows/stainless-CI.yml/badge.svg?branch=main)](https://github.com/epfl-lara/stainless/actions/workflows/stainless-CI.yml/?branch=main) [![Gitter chat][gitter-img]][gitter-ref] [![Apache 2.0 License][license-img]][license-ref]

Hosted at https://github.com/epfl-lara/stainless ; mirrored at https://gitlab.epfl.ch/lara/stainless . Check out also [Inox](https://github.com/epfl-lara/inox) and [Bolts](https://github.com/epfl-lara/bolts/).

Verification framework for a subset of the [Scala](http://scala-lang.org) programming language. See the [tutorial](https://epfl-lara.github.io/asplos2022tutorial/).

Please note that this repository uses `git submodules`, so you need to either:

- clone it with the `--recursive` option, or
- run `$ git submodule update --init --recursive` after cloning.

Please note that Stainless does not support Scala 2 frontend anymore, only Scala 3.5.0 and later. The latest release that  supports Scala 2.13 frontend is the [v0.9.8.7](https://github.com/epfl-lara/stainless/releases/tag/v0.9.8.7).

## Quick start

We test mostly on [Ubuntu](https://ubuntu.com/download); on [Windows](https://www.microsoft.com/eb-gb/software-download/windows10), you can get sufficient text-based Ubuntu environment by installing [Windows Subsystem for Linux](https://learn.microsoft.com/en-us/windows/wsl/install) (e.g. `wsl --install`, then `wsl --install -d ubuntu`). Ensure you have [Java](https://openjdk.org/projects/jdk/21/) 21 or later ready (it can be headless); on Ubuntu `sudo apt install openjdk-21-jdk-headless` suffices.

Once ready, [download the latest `stainless-dotty-standalone` release](https://github.com/epfl-lara/stainless/releases) for your platform. Unzip the archive, and run Stainless through the `stainless` script. Stainless expects a list of space-separated Scala files to verify but also has other [Command-line Options](https://epfl-lara.github.io/stainless/options.html).

To check if everything works, you may create a file named `HelloStainless.scala` next to the `stainless` script with the following content:
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
and run `stainless HelloStainless.scala`.
If all goes well, Stainless should report something along the lines:
```log
[  Info  ]   ┌───────────────────┐
[  Info  ] ╔═╡ stainless summary ╞════════════════════════════════════════════════════════════════════╗
[  Info  ] ║ └───────────────────┘                                                                    ║
[  Info  ] ║ HelloStainless.scala:6:5:   myTail  body assertion: match exhaustiveness  nativez3   0,0 ║
[  Info  ] ╟┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄╢
[  Info  ] ║ total: 1    valid: 1    (0 from cache) invalid: 0    unknown: 0    time:     0,0         ║
[  Info  ] ╚══════════════════════════════════════════════════════════════════════════════════════════╝
[  Info  ] Shutting down executor service.
```
If you see funny symbols instead of beautiful ASCII art, run Stainless with the `--no-colors` option for clean ASCII output with a standardized error message format.

The release archive of Stainless only requires JDK 21 or later. In particular, it needs
neither a Scala compiler nor SBT. It is shipped with Z3 5.4.1+, cvc5 1.4.2+ and
Princess (branch compiled for Scala 3). It includes the Z3 native API for Linux
(x64 and ARM64, glibc 2.39 or later), macOS (ARM64) and Windows (x64). Elsewhere,
Stainless falls back to the Z3 executable; use the option `--solvers=smt-z3` to
rely on the executable explicitly.

## Using Stainless as a compiler plugin (to verify and run programs)

The `stainless` script only verifies programs. To also compile and **run** a Stainless program, use
Stainless as a plugin of the Scala 3 compiler: Stainless verifies the program during compilation,
then the compiler produces the class files as usual. The Stainless library
(`ch.epfl.lara::stainless-library`) and the compiler plugin (`ch.epfl.lara:::stainless-dotty-plugin`)
are published on Maven Central (for releases after 0.10.5), so this works with any build tool and needs
no installation besides it. The plugin includes the Z3 native API and Princess, so no solver has to be
installed either.

With [Scala CLI](https://scala-cli.virtuslab.org/), put this `project.scala` next to your sources,
replacing `<stainless-version>` with the [latest release](https://github.com/epfl-lara/stainless/releases)
and `<scala-version>` with the version of Scala it is built with (the one of
[`examples/scala-cli/project.scala`](examples/scala-cli/project.scala), which is also in the name of the
plugin artifact on Maven Central, `stainless-dotty-plugin_<scala-version>`):
```scala
//> using scalaOrganization ch.epfl.lara
//> using scala <scala-version>
//> using dep ch.epfl.lara::stainless-library:<stainless-version>
//> using plugin ch.epfl.lara:::stainless-dotty-plugin:<stainless-version>
```
and run `scala --power run .` (the `scalaOrganization` directive needs `--power`). The plugin verifies
the program, removes its ghost code, and enables the compiler options Stainless needs. To run the
program without verifying it, add `//> using options -P:stainless:verify:false`.

Note that programs with qualified types may need the compiler option `-Yqualified-types-anf`
(`//> using options -Yqualified-types-anf`), for instance when Stainless reports that it does not
support a type with a refinement on a parameter. The plugin can't enable this option itself.

Note that verification failures are reported as warnings: they do not stop the compilation, so check the
verification summary before trusting a run.

The [`examples`](examples/) directory has minimal projects for Scala CLI and sbt, and the
[installation documentation](https://epfl-lara.github.io/stainless/installation.html#maven-central)
has the sbt configuration and more details.

## Build and Installation Instructions

Please refer to the [installation documentation here](https://epfl-lara.github.io/stainless/installation.html).

## Further Documentation and Learning Materials

The main documentation for Stainless is hosted at
https://epfl-lara.github.io/stainless/.

To get started with using Stainless, see videos:
  * [Stainless Introduction for 2nd year EPFL BSc students](https://mediaspace.epfl.ch/media/%5BCS214+W13+FP%5D+Formal+Verification+%282024-12-09%29/0_g7v3qvjp)
  * [ASPLOS'22 tutorial](https://epfl-lara.github.io/asplos2022tutorial/)
  * [FMCAD'21 tutorial](https://github.com/epfl-lara/fmcad2021tutorial/)
  * [Formal Verification Course](https://mediaspace.epfl.ch/channel/CS-550+Formal+Verification/30542):
    * [Getting Started](https://mediaspace.epfl.ch/media/01-02%2C+First+Steps+with+Stainless/0_tghlsgep/30542)
    * Four part tutorial: [1](https://mediaspace.epfl.ch/playlist/dedicated/30542/0_hrhu33vg/0_h1bv5a7v), [2](https://mediaspace.epfl.ch/playlist/dedicated/30542/0_hrhu33vg/0_io2c8cnl), [3](https://mediaspace.epfl.ch/playlist/dedicated/30542/0_hrhu33vg/0_j7fgd1oc), [4](https://mediaspace.epfl.ch/playlist/dedicated/30542/0_hrhu33vg/0_4soh944h)
    * [Assertions](https://mediaspace.epfl.ch/playlist/dedicated/30542/0_vw42tr2d/0_54yx91xi)
    * [Unfolding](https://mediaspace.epfl.ch/playlist/dedicated/30542/0_vw42tr2d/0_4byxmv9i)
    * [Dispenser Example](https://mediaspace.epfl.ch/playlist/dedicated/30542/0_hrhu33vg/0_omextd9i)
  * [Keynote at Lambda Days'20](https://www.youtube.com/watch?v=dkO59PTcNxA)
  * [Keynote at ScalaDays'17 Copenhagen](https://www.youtube.com/watch?v=d4VeFa0z_Lo)

 or see local [documentation](https://epfl-lara.github.io/stainless/) chapters, such as:
  * [Introduction to Stainless](https://epfl-lara.github.io/stainless/intro.html)
  * [Installation](https://epfl-lara.github.io/stainless/installation.html)
  * [Getting Started](https://epfl-lara.github.io/stainless/gettingstarted.html)
  * [Command-line Options](https://epfl-lara.github.io/stainless/options.html)
  * [Mini Tutorial](https://epfl-lara.github.io/stainless/tutorial.html)

There is also a [Stainless EPFL Page](https://stainless.epfl.ch) which hosts a mirror of the GitHub repository.

## License

Stainless is released under the Apache 2.0 license. See the [LICENSE](LICENSE) file for more information.

## Relation to [Inox](https://github.com/epfl-lara/inox)

Stainless relies on Inox to solve the various queries stemming from program verification.
Inox supports model-complete queries in a feature-rich fragment that lets Stainless focus
on program transformations and soundness of both contract and termination checking and uses its own reasoning steps, as well as invocations to solvers (theorem provers) [z3](https://github.com/Z3Prover/z3), [cvc5](https://cvc5.github.io/), and [Princess](http://www.philipp.ruemmer.org/princess.shtml).

[latest-release]: https://github.com/epfl-lara/stainless/releases/latest
[license-img]: https://img.shields.io/badge/license-Apache_2.0-blue.svg?color=134EA2
[license-ref]: https://github.com/epfl-lara/stainless/blob/main/LICENSE
[gitter-img]: https://img.shields.io/gitter/room/gitterHQ/gitter.svg?color=ed1965
[gitter-ref]: https://gitter.im/epfl-lara/stainless
[release-img]: https://img.shields.io/github/release-pre/epfl-lara/stainless.svg
[tag-date-img]: https://img.shields.io/github/release-date-pre/epfl-lara/stainless.svg?style=popout
