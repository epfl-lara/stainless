# Release Notes

## Version 0.9.9.0 (2024-12-09)

- Scala version is now 3.5.2 
- Update to Inox that supports Horn clause solving, https://github.com/epfl-lara/inox/pull/214
- Fix an extraction bug with type synonym definitions (#1595)
- Explicit measures in List library so termination checks are cached
- More properties and methods on lists and sets
- Set considered to have positive polarity (it is finite)
- Internal solver errors are now silent by default

## Version 0.9.8.9 (2024-10-19)

- Default cache now only stores SHA-256 hash of formulas ( -binary-cache=true for old version)
- Scala version is now 3.5.0
- Inox now has a solver for ground assertions based on internal evaluator (Inox #218), called `eval`
- Opaque Forall and ensures: help higher order contracts (#1567)
- Option `--compact` also reduces progress messages (#1573)
- Changed CI to use GitHub actions
- Documented a limited use of `throw`
- CI scripts as part of move to GitHub actions

## Version 0.9.8.8 (2024-08-22)

### Stainless frontend, library and internals

- Remove Scala 2 frontend (#1517)
- Transform `throw` into `assert(false)` (#1521)
- Add measure transfer for equivalence checking (#1557)
- Add further benchmarks for equivalence checking (#1538, #1554)
- Add SAT Check for precondition (#1548)
- Add various specifications to Stainless library (#1555, #1541)
- Enhance unfold to work on bindings and imperative code as well (#1533)
- Various bug fixes (#1531, #1532)

### Build

- Move Inox as a submodule instead of an http dependency (#1520)

### Documentation

- Add documentation for codespaces use and link to a sample repo (#1440)


## Version 0.9.8.7 (2024-05-06)

### Stainless frontend, library and internals

- Add `stainless.lang.Try` allowing for a monadic try construct (#1515)
- Upgrade the Scala 3 frontend to Scala 3.3.3 (#1514 and #1516)
- Avoid rebuilding mutated objects when possible in AntiAliasing (#1507 and #1509)
- Show the ID of the corresponding generated SMT-lib file for each VC in the summary when `debug=smt` option is enabled (#1508)
- Have `isExpressionFresh` consider arguments when computing freshness of a function call (#1505)
- Avoid pairwise matching of "external" methods in Equivalence checking mode (#1503)
- Fix in documentation (#1502)
- Add support for exported methods (#1501)
- Fix ImperativeCleanup phase to not clean some unused bindings that should not be removed (#1500)
- Fix a bug in Equivalence checking mode that was considering the wrong preconditions in some cases (#1499)
- Fix type alias of opaque triggering missing dependencies (#1498)
- Add missing dropVCs annotation in AntiAliasing (#1496)
- Relax fallback condition of AntiAliasing handling of Let (#1495)
- Add missing case for Array typeBounds, make private final, fix minor bug in RefinementLifting (#1494)
- Fix MatchError in EffectsAnalyzer leading to a crash in some cases (#1492)
- Fix parametric extension methods (#1490)
- Allow for redundant type checks for pattern matching (#1489)
- Add 'unknown safety' category for Equivalence checkign (#1488)
- Allows for let-binding in tests and output 'expected but got' results in Equivalence checking (#1485)
- Add a tail recursive implementation of `map` for mutable tail lists as a benchmark (#1484)

### Build

- Fix the `stainless-cli` script (#1486)

## Version 0.9.8.2 (2023-11-10)

### Stainless frontend, library and internals

- Add `stainless.lang.Cell` and `stainless.lang.swap`, allowing to swap the content of two `Cells` (#1461)
- Add support for cvc5 (#1444)
- Upgrade the Scala 3 frontend to Scala 3.3 (#1442)
- Upgrade the Scala 2 frontend to Scala 2.13.12 (#1469)
- Support for `new Array(len)` constructor for primitive types (#1453)
- Remove ensuring clause in ghost elimination (#1454)
- Fix while loops being mistakenly considered as ghost (#1467)
- Fix occasionally incorrect positions (#1447, #1455, #1473, #1477)
- Enforce purity for class invariants (#1475)
- Do not treat inline methods or functions as ghost (#1481)
- Applying some type widening in `ReturnElimination` to avoid triggering `AdtSpecialization` (#1466)
- Relax freshness condition and improve aliasing error messages (#1468)

### Build

- Upgrade the shipped Z3 version (`smt-z3`) to 4.12.2 (#1469)
- Add cvc5 1.0.8 to the archive (#1469)
- Add arm64 build for macOS (#1469)
- Add the compiled and source code of the Stainless library to the archive, under `lib` (#1469)
- Add a `stainless-cli` script to invoke scala-cli with the library (#1469)
- Rename `stainless.sh` to `stainless` (#1469)


## Version 0.9.8.1 (2023-09-21)

### Stainless frontend, library and internals

- Fix `--watch` crashing on compilation error (#1424)
- Expand options for equivalence checking (#1422, #1435)
- Add more info messages (#1425)
- Add further postconditions for indexOf and apply (#1428)
- Documentation updates (#1429, #1434, #1431)
- Fix ghost elimination for GenC (#1433)
- Reorganize some library files and allow for verification without Stainless library (#1436)
- Fix issue #1399


## Version 0.9.8 (2023-05-30)

### Stainless frontend, library and internals

- Expand Stainless library (#1400, #1402, #1418)
- Improved reporting (#1396, #1410)
- Support for enum case objects (#1384)
- Support `require` and `ensuring` message overloads (#1382)
- Make `ghost`, `assert` and `require` arguments by-name (#1364)
- Move equivalence checking to a component (#1378)
- Some improvements to OL and OCBSL based simplifiers (#1380)
- Fix issues #1343, #1214, #1351, #1352, #1353, #1365, #1379, #1389, #1390, #1377, #1349, #1405, #1401

## Version 0.9.7 (2022-11-21)

### Stainless frontend, library and internals

- Improve equivalence checking: function call matching, norm, mkTest (#1294)
- Experimental integration of OL- and OCBSL- based simplifiers (#1315)
- Upgrade to Scala 3.2 (#1317)
- Add verification pipeline summary (#1336)
- Fix issues #1332, #1271, #1333, #731, #1290, #1321, #1322, #1306, #1301, #1302

### Build

- Include macOS ScalaZ3 build
- Include SBT Stainless plugin


## Version 0.9.6 (2022-07-03)

### Stainless frontend, library and internals

- Fix issues #1268 #1269 #1270 #1272 #1273 #1274 (#1277)
- Avoid unnecessary capture of PC variables when hoisting functions (#1265)
- Minor fixes (#1260, #1263, #1280, #1292)

### GenC

- Annotate unexported function as `static` (#1261)


## Version 0.9.5 (2022-05-06)

### Stainless frontend, library and internals

- VC checking in parallel (#1247)
  - The parallelism can be specified with `-Dparallel=<N>` when invoking Stainless
- Fix issue #1159 (#1246)
- Address some issues in the imperative phase (#1245, #1252)

## Version 0.9.4 (2022-03-11)

### Stainless frontend, library and internals

- Pass the `-Ysafe-init` option to Dotty  (#1242)
- Experimental test cases generation (#1239)
- Fix issue #1051 (#1219)
- PC for local classes capturing variables (#1210)

### Build

- Do not duplicate ScalaZ3 jars (#1241)


## Version 0.9.3 (2022-02-25)

### GenC

- Add `cCode.noMangling` annotation and split defines into header and C files
- Propagate `volatile` and `static` keywords to struct fields
- Avoid trimming of `cCode.define` functions
- Introduce a binding to 'guard' against references created by the Referentiator (#1235)

### Build

- Windows build (#1234)

## Version 0.9.2 (2022-01-17)

### Stainless frontend, library and internals

- Main list operations with Int instead of BigInt indices (#1225)
- Scala 3 extraction frontend (#1216, `scala-3.x` branch only)
- Adapt Coq build to 8.14.0 (#1198)
- Improve handling of Enter key in watch mode (#1195)
- Fix extraction of f => g style renamed imports (#1193)
- Add sizes debug option to display size statistics after each phase (#1185)
- Remove simplifications in VC building to avoid big slowdown (#1184)

### GenC

- Split header and C includes (#1204)
- Better header extraction in GenC cCode.function annotation (#1203)
- Extract header from manually defined definition in Genc (#1200)
- Add missing assert cases in GenC deconstructors (#1199)
- Bump sbt-assembly version, more parentheses and relax arrays checks in GenC (#1197)
- Add support for initializing complex expressions with memset 0 (#1196)
- Fix GenC duplicate reporting and add cCode.define annotation (#1192)
- Fix some GenC export issues and add cCode.pack annotation (#1190)
- Remove parentheses from dropped constants in GenC (#1189)
- cCode.drop shouldn't always imply extern (#1188)
- Use primitive equality for TypeDefType in GenC (#1187)
- Fix typo in sizes debug output (#1186)

### Documentation

- Add documentation for some annotations and keywords (#1183)
- Doc fixes (#1220)
- Example with laws and dynamic dispatch (#1206)


## Version 0.9.1 (2021-09-28)

### Stainless frontend and internals

- Add the `&&&` operator, which splits verification conditions.
- Improve reporting when there are multiple `require` in inlined function
- Add some benchmarks for `full-imperative` phase
- Upgrade to Scala 2.13 (#1173)

### GenC

- Allow reference to old global state
- Ignore `opaque` keyword in GenC inlining


## Version 0.9.0 (2021-08-27)

### Stainless frontend and internals

- Add `--full-imperative` phase, for an imperative phase without aliasing restrictions (#1140)
- Bug fixes in imperative phase (#1108, #1103, #1116, #1121, #1123)
- Split `Unchecked` annotation into `DropVCs` and `DropConjunct` (#1125)
- Fix ghost elimination for multiple parameter groups (#1138)
- Fix timeout sometimes not being respected with non-incremental mode (`no-inc:` solver prefix) (#1141)
- Bump sbt to `1.5.5` and add documentation for Windows (#1134)

### GenC

- Drop extern functions in GenC (#1114)
- Disable mangling of fields for classes that are defined outside Stainless (#1115)
- Add pure attribute to pure functions when compiling to C (#1119)
- Split `inline` (for verification) and `cCode.inline` (for compilation) annotations (#1132)
- Reorganize GenC annotations (#1129)
- Bug fixes (#1124, #1133)


## Version 0.8.1 (2021-06-20)

### Stainless frontend and internals

- Better support for jumping to errors in IDEs (#966, #995, #996)
- Add support for return keyword (#923, #925, #934)
- Various fixes and changes in aliasing analysis (#915, #918, #920, #928, #965, #969, #973, #985, #1076, #1094)
- Support for tuples with mutable types (#1064)
- Add support for multiple requires in functions (not in ADTs) (#983)
- Better measure inference for chain processor (#967)
- Add more support for bitvector operations (#962, #1062)
- Print verification progress but not all verification conditions by default (#1018)
- Add support for swap operation for array elements (#946)
- Add support for inlining and making opaque while loops (#1009)
- Library cleanup (#953, #998, #999, #1000)
- Add fresh copy primitive (#1033)
- Improve traceInduct and add clustering (#1052)
- Add no-return invariants for while loops (#1079)

### SMT solvers

- Add support for CVC4 1.8 (#833)
- Add support for Z3 4.8.10 (#1010)

### GenC

- Better support for ``@export`` annotation in GenC (#924, #1008, #1019)
- Add StructInliningPhase to remove structs with one member in GenC (#1058, #1065)
- Add support for fixed length arrays in GenC (#1055, #1057)
- Add compilation of global state in GenC (#1085, #1089)


## Version 0.8.0 (2021-02-24)

### Features

- Support for Scala 2.12.13 (#913)
- Support for ghost fields in GenC (#904, #907)
- Initial support for unsigned integers in GenC (#888)

### Bug fixes

- Fix issues watch mode (and add support for Enter key to reload) (#906)
- Better support for refinement types in type-checker
- Various bug fixes in extraction phases


## Version 0.7.6 (2021-01-18)

### Features

- Add GenC component from Leon (#885)
- Add frontend for more bitvector types and operations (#879)

### Improvements

- Inox dependency is now directly on GitHub

### Bug fixes

- Fix some issues in imperative phase (#874) and type encoding (#884)


## Version 0.7.5 (2020-11-27)

### Features

- Add `admit-vcs` option to generate VCs without sending them to the solver
- Add support for indexed types in scalac frontend

### Improvements

- Generalize specification helpers (#828)

### Bug fixes

- Remove unsound type-checking rule for function types, and add subtying rules instead


## Version 0.7.4 (2020-10-02)

### Bug fixes

- Fix unapplyAccessor not instantiating with refinement type (#841)
- Remove duplicate serializations


## Version 0.7.3 (2020-09-08)

### Improvements

- Remove check that measure has good type at call site (this was making arguments of recursive functions being type-checked twice, and thus duplicating VCs)
- Instead, add check that mutually recursive functions have the same measure type
- `SplitCallBack` now processes mutually recursive functions together
- Improve HTML output for type-checking derivation


## Version 0.7.2 (29-08-2020)

### Features

- Add `ListMap` implementation (associative list) (#794)

### Improvements

- Remove type-checking tuple rule that was duplicating VCs (#792)
- Improve documentation on check/assert (#815)
- Add documentation for contracts on abstract functions (#825)

### Bug fixes

- Fix `@induct` transformation for bounded-size integers (#804)
- Add checks to reject programs not supported by Stainless (#810, #814)
- Fix type encoding translation error (#818)
- Fix issues on `@inlineInvariant` feature (#820)
- Fix bug where Stainless could make an infinite loop in `isMutableClassType` (#824)
- Fix "missing field" error in watch mode (#829)
- Fix bug in watch mode where errors from previous runs kept getting reported (#830)
- Fix bug in watch mode that made the verification report incomplete (#831)


## Version 0.7.1 (17-06-2020)

### Features

- Add `ListOps.noDuplicate`, and a contract for `Set#toList` (#746)
- Check match exhaustiveness in type checker (#737)

### Improvements

- Rearrange debugging options (#781)
- Change StdOut print functions to handle Any (#761)
- Improve error reporting (#756)
- Add `@inlineInvariant` flag to ADT invariant dispatch method (#744)
- Use static checks for `SetOps` methods (#742)
- Recommend using Z3 4.8.6 instead of 4.7.1 (#741)

### Bug fixes

- Fix `List#toScala` method (#778)

## Version 0.7.0 (07-02-2020)

### Features

- Enable `--type-checker` by default (#721)
- Rework the termination checker to infer measures for recursive functions (#721)

### Improvements

- Relax mutual recursion check for functions/ADTs enough for TypeEncoding (#721)
- Add `List#toScala` and `List.fromScala` to the library (#708)
- Add methods `map`, `withFilter`, `toList`, and `toScala` to `Set` (#708)
- Add methods `keys`, `values`, `toList` and `toScala` to `Map` (#708)

### Bug fixes

- Add missing position in `FieldAccessors` phase (#734)
- Fix extraction of extern types with Dotty frontend (#708)

## Version 0.6.2 (16-01-2020)

### Improvements

- Ensures invariants of ancestors cannot be weakened
- Limit parallelism when running stainless-actors tests
- Update Docker packaging script

### Bug fixes

- Fix broken benchmark in TypeCheckerSuite

## Version 0.6.1 (13-11-2019)

### Improvements

- Modularize Dockerfile and automate Docker image release process
- Specify version of extra deps when extracting sources from JAR
- Change name of target directory for extracted sources

## Bug fixes

- Add missing @library annotation to stainless-algebra. Bump to 0.1.1
- Fix missing import in stainless-algebra. Bump to 0.1.2

## Version 0.6.0 (07-11-2019)

### Features

- Enable strict arithmetic by default (#608)
- Introduce `stainless.math.wrapping` method to opt-out of overflow checks (#608)
- Add `@wrapping` annotation for function definitions (#608)
- Add ability to resolve extra source dependencies via Coursier (#715)
- Erase values classes (#712)
- Expose @invariant flag to user-land (#712)
- Lift invariants of value classes to a refinement type (#712)
- Implement Map#-- for finite maps (#705)
- Add List.empty method

### Improvements

- Enforce overriding of abstract vals with constructor params (#712)
- Ensure soundness of invariants in TreeSanitizer (#712)
- Lift refinements in lets into assertions (#712)
- Update ScalaZ3 to its latest release (bundling Z3 4.7.1) (#707)
- Disallow defining classes within a class body (#697)
- Document type aliases and type members (#686)
- Ensure type parameters with non-trivial bounds are properly encoded (#685)

### Bug fixes

- Fix null pointer exception when running --eval (#699)
- Fix warning about multiple library sources (#692)

## Version 0.5.1 (12-09-2019)

### Bug fixes

- Fix bug in ScalaCompiler.topmostAncestors (#693)
- Fix warning about multiple library sources (#692)

## Version 0.5.0 (12-09-2019)

### Features

- Bump Scala version to 2.12.9 and update sbt to 1.3.0 (#629, #591)
- Add support for removing elements from Map (#688)
- Setting `stainlessEnabled := false` keeps both library sources and ghost elimination (#684)
- Include Stainless library sources even when verification is disabled in sbt plugin (#680)
- Add --config-file option to specify or disable configuration file (#648)

### Improvements

- Document type aliases and type members support (#686)
- Add Cont monad benchmark to model exceptions (#675)
- Make qed be of unit type with post-condition (#669)
- Do not consider built-in classes in override chain (#661)
- Induct flag only adds decreases check if type checker is enabled (#657)
- Improve position reporting for postconditions (#656)
- Remove warnings for asserts in extern functions (#651)
- Propagate @ghost annotation to variables introduced by calls to default copy getter (#643)

### Bug fixes

- Fix bad mutual recursion in GodelNumbering proof (#679)
- Ensure type parameters with non-trivial bounds are properly encoded (#685)
- Do not check model when invoking solver during partial evaluation (#676)

## Version 0.4.0 (23-08-2019)

### Features

- Support for type members in local classes (#633)
- Report functions with missing positions in PositionChecker (#639)
- Add AmortizedQueue data structure to Stainless library (#635)
- Add debug section to show the full VC before simplification (#637)
- Add script to run tests on stainless-actors and bolts (#623)
- Ignore @library flag on typeclasses which have non-library subclasses (#595)
- Enable -feature and -unchecked scalac flags in embedded compiler (#610)
- Enforce sound equality tests (#605, #609)
- Port partial specification feature from Leon (#438)
- Add BoundedQuantifiers module to the library (#596)

### Improvements

- Propagate @ghost annotation to variables introduced by calls to default copy getter (#643)
- Do not lift refinement into pre-/post-conditions when `--type-checker` is enabled (#620)
- Follow symbolic links when searching for base directory (#621)
- Check that methods are only overridden by methods with the same ghostiness (#615)
- Check that required tools are installed before packaging (#599)
- Add readability check for jars in script (#600)

### Bug fixes

- Add missing serializer for LocalThis (#631)
- Fix malformed case object constructor method (#641)
- Use triple quotes and escape \u for extraClasspath and extraCompilerArguments (#626)
- Fix bug in AssertionInjector where unary minus was lost in strict arithmetic mode (#630)
- Fix DottyVerificationSuite not being run (non-initialized folder) (#627)
- Fix bug where anonymous inner classes would have same identifier (#619)
- Fix handling of super calls in case objects  (#618)
- Fix a bunch of issues with type members (#580)

## Version 0.3.2 (16-06-2019)

### Improvements

- Improve support for type members and type aliases (#580)

## Version 0.3.1 (09-06-2019)

### Features

- Re-enable check for abstract methods overrides and consider methods of abstract classes with empty body to be abstract (#587)

### Improvements

- Add documentation about the Gitter8 template, and re-order some sections (#588)
- Dealias type aliases more eagerly (#585)
- Add microtests from recently closed issues (#578)
- Add testcase for #532 (#589)

## Version 0.3.0 (02-06-2019)

### Features

- Indexed recursive types and type-checking based VC generation (#479)
- Display counter-examples when using metals (#579)
- Add --no-colors option, for use via metals in VS Code
- Add FAQ extracted from the C4DT newsletter (#570)
- Emit warning when dropping require/ensuring/assert in a user @extern function (#562)

### Improvements

- Microtests from recently closed issues (#578)
- Use git-describe to compute version of artifact in packaging script
- Bump Inox version to 1.1.0-332-ga6cbf8e (#571)
- Make purity of requires and assertions depend on their bodies (#547)

### Bug fixes

- Fix "a required artifact is not listed by module descriptor" error
- Fix report being shown twice (#567)
- Update sbt docs and fix plugin publishing issues (#565)
- Fix effects checker for MutableMapUpdated tree (#563)

## Version 0.2.2 (25-06-2019)

- Fix sbt plugin, metals integration, and tests (#556)
- Switch to git-describe based versioning scheme (#550)
- Add `--version` flag (#550)

## Version 0.2.1 (18-06-2019)

- Fix license in sbt build definition (#545)
- Prevent over-simplifications in ImperativeCodeElimination (#533)
- Fix check in mutable map effect analysis (#525)
- Bump Inox version to 1.1.0-329-g3c23a86 (#530)

## Version 0.2-cfac3aaf (28-05-2019)

- Change license from AGPL to Apache 2.0
- Allow specifying which arguments should the induction be performed over with `@induct` (#504)
- Add `snapshot` keyword for imperative code (#491)
- Add `@keep` annotation and option to avoid filtering out library symbols (#488)
- Add packaging script for stainless-scalac-standalone (#487)
- Add support for type aliases, type members, and dependent function types (#470)
- Support for configuration file (#466)
- Extract default getters in toplevel objects (#464)
- Report positions when going through the compiler reporter from the sbt plugin (#434)
- Bump Scala to v2.12.8 (#437)
- Upgrade Dotty to 0.12.0-RC1 (#436)
- Fix for line numbers sometimes being off (#429)
- Remove registry and add option to consolidate all symbols into a single symbol table (#422)
- Help solver deduce that reified type args do not influence evaluation (#414)
- Allow fields/methods named after tuple selectors (#410)
- Remove all assertions, and use assumeChecked for simplifications (#408)
- Add `Nat` type to the library (#407)
- Conditional effect targets for accessors, mutable Any, and phase re-ordering (#399)
- Add mechanism to recover from missing dependencies (#397)
- Add while-loop condition and invariant to path condition in TransformerWithPC (#392)
- Make equations go backwards for better line number reporting (#341)
- Add support for inner and anonymous classes (#271)

## Version 0.1-93dbd33 (14-01-2019)

- First official release on GitHub
