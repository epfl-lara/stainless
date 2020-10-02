# Release Notes

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

