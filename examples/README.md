# Using Stainless from Maven Central

These two minimal projects verify (and run) the same program, `Example.scala`, with the Stainless
artifacts published on Maven Central under `ch.epfl.lara`:

- `stainless-library_3`, the Stainless library, as a regular binary dependency: Stainless extracts
  the definitions it needs from the TASTy files of the JAR,
- `stainless-dotty-plugin_<Scala version>`, Stainless itself, as a plugin of the Scala 3 compiler
  (it bundles Inox and the rest of Stainless).

Both need the Scala 3 compiler of the lab (`ch.epfl.lara`, also on Maven Central), in the exact
version Stainless is built with. No SMT solver has to be installed: the plugin includes the native
interface of Z3 (for Linux x64 and ARM64, macOS ARM64 and Windows x64; elsewhere, it needs `z3` or
`cvc5` on the `PATH`, see the
[documentation](https://epfl-lara.github.io/stainless/installation.html#smt-solvers)).

Replace the version of Stainless in `project.scala` and `build.sbt` by the
[latest one](https://github.com/epfl-lara/stainless/releases).

## Scala CLI

```
cd scala-cli
scala --power compile .   # verifies and compiles
scala --power run .       # runs the program, without its ghost code
```

`--power` is needed for the `scalaOrganization` directive of `project.scala`; `scala config power
true` enables it once and for all.

## sbt

```
cd sbt
sbt compile   # verifies and compiles
sbt run
```

`build.sbt` uses the compiler plugin directly. The [sbt plugin of
Stainless](https://epfl-lara.github.io/stainless/installation.html#sbt-project), `sbt-stainless`,
is an alternative that is not on Maven Central.

## Notes

- Verification runs as a phase of the compiler, on every compilation. The verification conditions
  that don't hold are reported as warnings: they don't fail the compilation.
- The plugin enables the compiler options Stainless needs (`-Yretain-trees`, to read the
  definitions of the library from its TASTy files, and the language features of qualified types).
- Verification and ghost code elimination are on by default: `-P:stainless:verify:false` turns
  verification off, e.g. to only compile and run, and `-P:stainless:ghost-elim:false` keeps the ghost
  code.
- Programs with qualified types may need the compiler option `-Yqualified-types-anf` (e.g. when
  Stainless reports that it does not support a type with a refinement on a parameter): the
  plugin can't enable it, because the compiler decides whether to run its phases before loading the
  plugin.
- `./test.sh <version>` verifies and runs both projects with the given version of Stainless, e.g.
  the one of the working tree after `sbt stainless-library/publishLocal
  stainless-dotty-plugin/publishLocal`.
