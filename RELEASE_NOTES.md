
# Release Notes

## Unreleased

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

