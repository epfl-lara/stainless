# `old(...)` in refinement types on function return types

## Summary

Refinement types on function return types play the role of postconditions, but until now they
could not refer to the *pre-state* of mutable arguments. This change adds support for the
`old(...)` construct in the refinement of a function's return type, with exactly the same
semantics and restrictions as `old(...)` in an `ensuring` clause:

```scala
case class Box(var x: BigInt)

// New: refinement-type style
def addX(b: Box, y: BigInt): { res: Unit with b.x == old(b).x + y } =
  b.x = b.x + y

// Equivalent ensuring style
def addXEnsuring(b: Box, y: BigInt): Unit = {
  b.x = b.x + y
}.ensuring(_ => b.x == old(b).x + y)
```

Refinement types are *not* translated into an `ensuring` clause: the `old` semantics is added
directly to the existing treatment of refinement types in the imperative phases, reusing the
same substitutions that the `ensuring` path uses.

## How it works

In the default imperative pipeline, `AntiAliasing` makes effects explicit: a function mutating
a parameter `b` is rewritten to return a tuple containing the updated value of `b`, and its
return type becomes a `SigmaType` binding a fresh variable `b'` for the post-state
(`EffectsAnalyzer.getReturnType`). In a postcondition, `AntiAliasing` rewrites (with the
non-recursive `replaceSingle`): `old(b) -> b` (the parameter, which after the transformation
always holds the pre-state) and `b -> b'` (the post-state).

This change applies the *same* substitution to refinement predicates in the return type:

- `old(p) -> p` for every parameter `p` (for unmutated parameters this yields `old(p) = p`,
  as in `ImperativeCodeElimination.rewriteSpecs`), and
- `p -> p'` (the fresh sigma binder) for every mutated parameter,

so `{ res: Unit with b.x == old(b).x + y }` becomes `Σ(b': Box). { res: Unit with b'.x == b.x + y }`,
which the type checker verifies against the transformed body — exactly the VC the `ensuring`
path generates.

## Changes

All changes are in the imperative extraction phases:

- `core/src/main/scala/stainless/extraction/imperative/EffectsAnalyzer.scala`
  - `getReturnType` now eliminates `old` as described above. The substitution is factored
    into a `ParamSubstituter` used by two new helpers, `substReturnType` and `substBody`.
  - `substBody` applies the same rewriting to the *casts to the return type* that the
    front end inserts in the function body (the compiler's qualified-types ANF encoding
    casts the body to the declared refined type). `old` is only rewritten inside types
    that are equal to the declared return type; anywhere else it is left untouched so that
    invalid usages are still reported.

- `core/src/main/scala/stainless/extraction/imperative/AntiAliasing.scala`
  - `updateFunction` uses the new helpers for the body and for the intermediate result binder,
    instead of plain `replaceFromSymbols` (which would incorrectly rewrite `old(b)` to the
    post-state `old(b')`).
  - New `bindCallSiteType` used in `mapApplication`: the binder for a call result is now typed
    with the callee's parameters substituted by the actual arguments, matching how the type
    checker infers invocation types (`insertFreshLets`). Refinements referring to arguments
    that are not referentially transparent are conservatively widened. This also fixes a
    pre-existing issue where *any* call to a parameter-mutating function with a refined return
    type produced a spurious invalid "refinements checks for subtyping" VC (reproducible on
    `main` without `old`); without this fix, callers could not use the postcondition at all.
    This is a completeness fix only: the binder type is still checked against the inferred
    invocation type, so a wrong substitution could only produce spurious failures, never
    unsoundness.

- `core/src/main/scala/stainless/extraction/imperative/EffectsChecker.scala`
  - New `checkReturnTypeRefinement`, enforcing on return-type refinements the same two checks
    that `checkEffectsLocations` enforces on `Ensuring`: the predicate must have no effects,
    and it may not mutate the pre-state under `old` (checked on the predicate with `old(e)`
    replaced by `e`, as for postconditions: "Postcondition tries to mutate old(b)").

- `core/src/main/scala/stainless/extraction/imperative/ImperativeCleanup.scala`
  - New `checkNoOldInTypes`: valid occurrences of `old` in types have been eliminated by
    `AntiAliasing` at this point, so any `old` remaining in a refinement type (e.g. in a
    parameter type or in the type of a local `val`) is reported with a proper error message,
    mirroring `checkNoOld`/`checkValidOldUsage` for expressions. Previously such programs
    crashed the pipeline with an internal error (`key not found: class Trees$Old`).

## Restrictions (same as `ensuring`)

- `old` is only allowed in the refinement of a function's *return type* (the "postcondition"
  position). In parameter refinements, local `val`/`var` refinements, or anywhere else in a
  type, it is rejected: *"In refinement types, Stainless `old` can only occur in the refinement
  of a function return type, applied to `this` or parameters."*
- `old` can only be applied to `this` and variables (enforced by the front end, as before).
- The refinement predicate may not have effects, and may not mutate the state under `old(...)`.

## Known limitations

- `old(this)` works (after method lifting, `this` is an ordinary parameter):

  ```scala
  case class Box(var x: BigInt):
    def bump(): { res: Boolean with old(this).x + 1 == this.x } =
      x = x + 1
      true
  ```

  However, the Scala compiler's qualified-types checker (independently of `old`) requires
  field accesses in qualifiers to be written with an explicit `this` prefix (`this.x`, not
  `x`), and rejects references to local variables of enclosing functions in qualifiers
  ("Invalid qualifier", before Stainless runs). Postconditions over such local variables
  (as in the `NestedOld` benchmarks) must therefore use `ensuring`.
- The experimental `--full-imperative` pipeline does not support `old` in refinement types;
  such programs are rejected with the error message above.

## Tests

- `frontends/benchmarks/refinement/valid/RefinementOld.scala`: `old(this)` on a method,
  `old` on a mutated parameter, the `ensuring` equivalent, callers using the postcondition
  in both styles, and `old` on an unmutated parameter.
- `frontends/benchmarks/refinement/invalid/RefinementOld.scala`: wrong postconditions using
  `old` (on a method with `old(this)` and on a function) must be reported invalid (soundness).
- `frontends/benchmarks/extraction/invalid/OldInParamRefinement.scala`,
  `OldInValRefinement.scala`, `OldMutationInRefinement.scala` (with `.check` files): invalid
  positions and mutation of the pre-state are rejected with the same errors as the
  `ensuring` counterparts.
- Documentation updated in `core/src/sphinx/refinementtypes.rst`.

Test suites run: `RefinementSuite` + `RefinementSuitePartial` (37/37), `ImperativeSuite`
(313/313), `DottyExtractionSuite` (all benchmark directories re-extracted).
