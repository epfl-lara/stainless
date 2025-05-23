# Stainless [![Release][release-img]][latest-release] [![Nightly Status](https://github.com/epfl-lara/stainless/actions/workflows/stainless-nightly.yml/badge.svg)](https://github.com/epfl-lara/stainless/actions/workflows/stainless-nightly.yml) [![Build Status](https://github.com/epfl-lara/stainless/actions/workflows/stainless-CI.yml/badge.svg?branch=main)](https://github.com/epfl-lara/stainless/actions/workflows/stainless-CI.yml/?branch=main) [![Gitter chat][gitter-img]][gitter-ref] [![Apache 2.0 License][license-img]][license-ref]

Hosted at https://github.com/epfl-lara/stainless ; mirrored at https://gitlab.epfl.ch/lara/stainless . Check out also [Inox](https://github.com/epfl-lara/inox) and [Bolts](https://github.com/epfl-lara/bolts/).

Verification framework for a subset of the [Scala](http://scala-lang.org) programming language. See the [tutorial](https://epfl-lara.github.io/asplos2022tutorial/).

Please note that this repository uses `git submodules`, so you need to either:

- clone it with the `--recursive` option, or
- run `$ git submodule update --init --recursive` after cloning.

Please note that Stainless does not support Scala 2 frontend anymore, only Scala 3.5.0 and later. The latest release that  supports Scala 2.13 frontend is the [v0.9.8.7](https://github.com/epfl-lara/stainless/releases/tag/v0.9.8.7).

## Quick start

We test mostly on [Ubuntu](https://ubuntu.com/download); on [Windows](https://www.microsoft.com/eb-gb/software-download/windows10), you can get sufficient text-based Ubuntu environment by installing [Windows Subsystem for Linux](https://learn.microsoft.com/en-us/windows/wsl/install) (e.g. `wsl --install`, then `wsl --install -d ubuntu`). Ensure you have a [Java](https://openjdk.org/projects/jdk/17/) version ready (it can be headless); on Ubuntu `sudo apt install openjdk-17-jdk-headless` suffices.

Once ready, [Download the latest `stainless-dotty-standalone` release](https://github.com/epfl-lara/stainless/releases) for your platform. Unzip the archive, and run Stainless through the `stainless` script. Stainless expects a list of space-separated Scala files to verify but also has other [Command-line Options](https://epfl-lara.github.io/stainless/options.html).

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
If you see funny symbols instead of beautiful ASCII art, run Stainless with the `--no-colors` option for clean ASCII output with a standardized error message format.

The release archive of Stainless only requires JDK17. In particular, it needs neither a Scala compiler nor SBT.
It is shipped with Z3 4.12.2+, cvc5 1.0.8+ and Princess (branch compiled for Scala 3). If Z3 API is not found, use option `--solvers=smt-z3` to rely on the executable instead of API call to z3.

## SBT Stainless plugin

Alternatively, one may integrate Stainless with SBT.
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

ThisBuild / scalaVersion := "3.5.2"

lazy val myTestProject = (project in file("."))
  .enablePlugins(StainlessPlugin) // <--------
  .settings(
    name := "Test"
  )
```

Verification occurs with the usual `compile` command.

Note that this method only ships the Princess SMT solver. Z3 and cvc5 can still be used if their executable can be found in the `$PATH`.

## Build and Use

To start quickly, install a JVM and use a [recent release](https://github.com/epfl-lara/stainless/releases). To build the project, run `sbt universal:stage`. If all goes well, scripts are generated for the front end:
  * `frontends/dotty/target/universal/stage/bin/stainless-dotty`

Use one of these scripts as you would use `scalac` to compile Scala files.
The default behavior of Stainless is to formally verify files, instead of generating JVM class files.
See [frontends/benchmarks/verification/valid/](frontends/benchmarks/verification/valid/) and related directories for some benchmarks and
[bolts repository](https://github.com/epfl-lara/bolts/) for a larger collection.
More information is available in the documentation links.

### SSH and VSCode

Visual Studio Code offers a feature allowing to connect to a host over SSH and edit code located on this host. This is useful to edit code on a remote machine using the local Visual Studio Code editor and running Stainless on this remote machine. See [this official documentation](https://code.visualstudio.com/docs/remote/ssh) to learn more about this feature.

If you have access to a remote machine over SSH, this is the recommended way to use Stainless. Please note you have to install Stainless on the remote machine following the instructions above.

### Github Codespaces

Github Codespaces
To allow running Stainless with only a browser, we have provided a sample repository to use Stainless with Github Codespaces. Github Codespaces are cloud machines that can be access via Visual Studio Code locally or in the browser. In our experience (as of October 2023), this flow works well, given the provided Ubuntu Linux virtual machines with 16GB of RAM and substantial processing power. Please see [this repository](https://github.com/samuelchassot/Stainless-codespaces) for further details.

### Snap Store

A package for Stainless is available on the Snap store as [`stainless`](https://snapcraft.io/stainless) with an experimental edge release. It can be used to install and run Stainless on any Snap enabled system (e.g. Ubuntu).

In a terminal, you can type:

```shell
sudo snap install stainless --edge
```

This exposes two commands, the tool `stainless`, as well as `stainless.cli`, running `scala-cli` with Stainless libraries loaded.

Running the commands the first time may take some time as some Scala libraries are downloaded.

### Arch User Repository

A package for Stainless is available on the Arch User Repository (AUR) for ArchLinux as [`stainless-git`](https://aur.archlinux.org/packages/stainless-git), which follows the latest commit on the `main` branch.
You can use your favorite AUR helper (we've tried `yay`, see [AUR Helpers](https://wiki.archlinux.org/title/AUR_helpers)),
or follow the [detailed instructions as on the ArchWiki](https://wiki.archlinux.org/title/Arch_User_Repository#Installing_and_upgrading_packages) to install the package.


For quick reference, with `yay` (or other AUR helpers accordingly):

```shell
yay -S stainless-git
```

and manually:

```shell
git clone https://aur.archlinux.org/stainless-git.git
cd stainless-git
makepkg -si
```

The option `-s` acquires dependencies (`java`, `git`, `sbt`) using `pacman`, `-i` installs Stainless system-wide.
Omit `-i` to avoid installing system-wide, and only perform a local build in the directory.

The solver packages `z3`, `cvc4`, and `cvc5`<sup>AUR</sup> can be added as optional dependencies, and having at least one is recommended for general use.

Issues with the package build should ideally be reported on the [AUR package page](https://aur.archlinux.org/packages/stainless-git) itself.

## Further Documentation and Learning Materials

To get started, see videos:
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

There is also a [Stainless EPFL Page](https://stainless.epfl.ch).

## License

Stainless is released under the Apache 2.0 license. See the [LICENSE]() file for more information.
---

### Relation to [Inox](https://github.com/epfl-lara/inox)

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
