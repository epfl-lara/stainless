# Internal mutation in the Stainless pipeline

New phases/checks are marked `<== NEW`, existing ones touched by the feature `<== touched`.

```
 Scala source
     │
     ▼
 ┌─ frontend (dotty) ────────────────────────────────────────────────────────────────┐
 │  FragmentChecker ........ @internallyMutable only on constructor fields    <== NEW │
 │  CodeExtraction ......... sameAs placement + argument is a call           <== NEW │
 │                           infer IsObservationallyPure flag                 <== NEW │
 │                           @internallyMutable field must be private         <== NEW │
 └───────────────────────────────────────────────────────────────────────────────────┘
     │
     ▼
 xlang ── PartialFunctions, XlangLowering
     │
     ▼
 innerclasses ── InnerClasses
     │
     ▼
 ┌─ methods (classes still present, `this` explicit) ──────────────────────────────┐
 │  InternallyMutableFields  check field accesses, ==, patterns, copy       <== NEW │
 │  ObservationallyPureCalls check f outside IM classes, m concrete        <== NEW │
 │                           o.m(a) ──► assert(pre_m); f(...)              <== NEW │
 │  Laws, SuperInvariants, SuperCalls, Sealing                                     │
 │  MethodLifting .......... methods become functions, `this` ──► `thiss`          │
 │  MergeInvariants, FieldAccessors, ValueClasses                                  │
 └─────────────────────────────────────────────────────────────────────────────────┘
     │
     ▼
 throwing ── ExceptionLifting
     │
     ▼
 ┌─ imperative (default) ───────────────────┐  ┌─ imperative (--full-imperative) ─────┐
 │  SameAsLowering            <== NEW       │  │  SameAsLowering            <== NEW   │
 │    callee is @pure                       │  │  EffectElaboration                   │
 │    sameAs(f(x))(res) ──► res==f(old(x))  │  │  ImperativeCodeElimination           │
 │  EffectElaboration (drops defs only)     │  │  ImperativeCleanup       <== touched │
 │  AntiAliasing                            │  └──────────────────────────────────────┘
 │    GhostChecker                          │
 │    EffectsChecker          <== touched   │
 │      obs-pure: effects only on IM fields  │
 │  ReturnElimination                       │
 │  ImperativeCodeElimination (removes old) │
 │  ImperativeCleanup         <== touched   │
 │    drops IM / obs-pure flags              │
 └──────────────────────────────────────────┘
     │
     ▼
 oo ── AdtSpecialization, TypeEncoding, InvariantInitialization
     │
     ▼
 innerfuns ── FunctionClosure ──► inlining ──► trace ──► verification
```

## What happens where

| Phase | Kind | Effect |
|---|---|---|
| `FragmentChecker` | check | `@internallyMutable` only on constructor fields (not methods, params, locals). |
| `CodeExtraction` | check + flag | `sameAs` only as top-level postcondition conjunct applied to `res`, argument must be a call. Adds `IsObservationallyPure`. IM fields must be `private`. |
| `InternallyMutableFields` | check | IM fields accessed only on `this`, from obs-pure / ghost / invariant methods of their class (calls to accessors and `copy$default$n` count). No pattern binding. No `==`/`!=` on types reaching an IM class. |
| `ObservationallyPureCalls` | check + rewrite | `f` not a method of an IM class; obs-pure method and its class concrete. `o.m(a)` ──► `val p = a; assert(pre_m); f(...)` (receiver bound only if used or not a variable). Calls on `this` inside obs-pure / ghost / invariant methods of the class are kept. |
| `SameAsLowering` | check + rewrite | `f` must be `@pure`. `sameAs(f(x))(res)` ──► `res == f(old(x))`, `old` on all params (incl. `thiss`). |
| `EffectsChecker` (in `AntiAliasing`) | check | Obs-pure functions only have effects on IM fields. `@pure` callee of `sameAs` really is pure. |
| `ImperativeCleanup` | cleanup | Drops `IsInternallyMutable` and `IsObservationallyPure`. |

## Why this order

- `InternallyMutableFields` and `ObservationallyPureCalls` must run **before `MethodLifting`**: they need `IsMethodOf`, class structure, and an explicit `this`.
- `InternallyMutableFields` runs **before** `ObservationallyPureCalls`, so it checks user code, not the generated replacements.
- `SameAsLowering` runs **first in the imperative pipelines**, so the usual `old` elimination applies to the lowered postcondition.
- `EffectsChecker` runs **after** the call replacement: callers of `o.m` have no effects left to report.

## Caveat

`--full-imperative` does not run `AntiAliasing`, hence no `EffectsChecker`: the "obs-pure only mutates IM fields" and `@pure` checks are not enforced there.
