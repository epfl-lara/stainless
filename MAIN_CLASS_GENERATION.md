# The `stainless.Main` class

> **Note:** `stainless.Main` used to be *generated* by an sbt source generator in `build.sbt`, a leftover of the era when Stainless had two frontends (scalac and dotty) sharing `frontends/common`, each needing its own `Main` wired to its own compiler `Factory`. With only the dotty frontend remaining, the generator was replaced by a hand-written class and the related build machinery was removed.

## Current setup

`stainless.Main` is a regular, hand-written source file: [frontends/dotty/src/main/scala/stainless/Main.scala](frontends/dotty/src/main/scala/stainless/Main.scala). It fills in the three pieces the driver needs:

1. **The compiler version** — `BuildInfo.scalaVersion`, i.e. `stainlessScalaVersion` from [build.sbt](build.sbt): Stainless is compiled with the same compiler it bundles as its frontend. `Main.compilerVersion` is also used by `DottyCompiler` and by test utilities.

2. **The Stainless library file list** — the library sources under `frontends/library/stainless` are shipped as classpath resources by a **resource generator** in `frontendSettings` ([build.sbt](build.sbt)), which also emits an index resource `stainless/libfiles.txt` listing their relative paths. `Main` reads that index from the classpath and passes the paths to the frontend factory; `frontend.FrontendFactory.libraryFiles` then resolves each path via the classloader (extracting to temp files when running from a jar).

3. **The frontend factory** — `frontends.dotc.DottyCompiler.Factory` (defined in [frontends/dotty/src/main/scala/stainless/frontends/dotc/DottyCompiler.scala](frontends/dotty/src/main/scala/stainless/frontends/dotc/DottyCompiler.scala)), instantiated directly.

All the actual driver logic lives in `trait MainHelpers` ([core/src/main/scala/stainless/MainHelpers.scala](core/src/main/scala/stainless/MainHelpers.scala), extending `inox.MainHelpers`), which declares `val factory: frontend.FrontendFactory` as abstract. `MainHelpers.main` parses options, builds the frontend via `frontend.build(ctx, compilerArgs, factory)`, and runs the verification cycle (with optional `--watch` mode).

## Packaging

- `stainless-dotty-standalone` sets `assembly / mainClass := Some("stainless.Main")` so the assembled fat jar's manifest points at the class.
- `stainless-dotty` itself uses `JavaAppPackaging`, which auto-discovers the same main class.

## What was removed in the cleanup

- The `Compile / sourceGenerators` task that wrote `Main.scala` into `sourceManaged`, including the `removeSlashU` escaping hack.
- The `frontendClass` setting key (each frontend used to name its compiler wrapper; the factory is now referenced directly).
- The runtime override that read a `libfiles.txt` from the current working directory (and the checked-in root `libfiles.txt`, plus the `libFilesFile`/`regenFilesFile` build machinery). The index is now always the one packaged with the build.
- The `frontendDottyVersion` and `stainlessLibScalaVersion` aliases of `stainlessScalaVersion` (per-frontend/per-library versions only made sense with two frontends). The `stainlessLibScalaVersion` *BuildInfo key* of `sbt-stainless` is kept, since the plugin code reads it.
- Unused build machinery: the `extraClasspath`/`scriptPath` task keys with `scriptSettings`, and the OS-detection vals (`isUnix`, `osName`, `osArch`, ...).

In a follow-up cleanup, the `frontends/common` source tree (shared between the two frontends and wired into `stainless-dotty` via `unmanagedSourceDirectories`) was folded into `frontends/dotty/src`: its `test` and `it` sources moved to the standard sbt locations (`frontends/dotty/src/test/scala`, `src/test/resources`, `src/it/scala`), and the `unmanagedSourceDirectories` wiring was removed. (`frontends/common/src/main/scala` had already been emptied earlier.) Only the `frontends/benchmarks` resource directory is still wired in from outside the project, since benchmarks are shared with other tooling.

---

## Appendix: the previous (generated) setup, for posterity

Before the cleanup, there was no hand-written `Main.scala`. It was produced by an sbt **source generator** defined in `commonFrontendSettings(compilerVersion: String)` in `build.sbt`, which ran for each frontend project (by then only `stainless-dotty`, which enabled it with `commonFrontendSettings(frontendDottyVersion)`).

At compile time, the generator task wrote `stainless/Main.scala` into `sourceManaged` (i.e. `frontends/dotty/target/scala-<version>/src_managed/main/stainless/Main.scala`). The generated object looked like this:

```scala
package stainless

object Main extends MainHelpers {
  val compilerVersion = "3.10.0-RC1-bin-20260608-cf86bba-NIGHTLY"

  override protected def displayVersion(reporter: inox.Reporter): Unit = {
    super.displayVersion(reporter)
    reporter.info(s"Bundled Scala compiler: $compilerVersion")
  }

  val defaultPaths = List("""stainless/proof/BoundedQuantifiers.scala""", ...)
  val libPaths = try {
    // read libfiles.txt from the current working directory
    val source = scala.io.Source.fromFile("libfiles.txt")
    try source.getLines().toList finally source.close()
  } catch {
    case (_: Throwable) => defaultPaths
  }

  override val factory = new frontends.dotc.DottyCompiler.Factory(Nil, libPaths)
}
```

Three things were baked into the generated source:

1. **The compiler version** — the `compilerVersion` parameter passed to `commonFrontendSettings`, i.e. `frontendDottyVersion` (an alias of `stainlessScalaVersion`).

2. **The Stainless library file list** — the `libraryFiles(...)` helper globbed all `*.scala` files under `frontends/library/stainless` and their relative paths were embedded as the `defaultPaths` string literals. At runtime, `Main` first tried to read `libfiles.txt` from the current working directory (an override mechanism; a copy of the file was also checked in at the repo root, regenerable via a `regenFilesFile` flag in `build.sbt`), falling back to the embedded list. A `removeSlashU` helper escaped `\u` sequences so Scala wouldn't interpret them as unicode escapes inside the generated source. The companion resource generator copying the library sources into managed resources already existed (it survives in today's setup, extended to also emit the `stainless/libfiles.txt` index).

3. **The frontend factory** — the `frontendClass` setting key (`"dotc.DottyCompiler"` for the dotty project, historically `"scalac.ScalaCompiler"` for the scalac one) was spliced in to instantiate `frontends.<frontendClass>.Factory`.

The design rationale: with two frontends (scalac and dotty) sharing `frontends/common`, each needed its own `Main` wired to its own compiler `Factory` and bundled compiler version — the generator parameterized that per-frontend.
