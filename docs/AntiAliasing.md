# The `AntiAliasing` Phase

`core/src/main/scala/stainless/extraction/imperative/AntiAliasing.scala`

## 1. Where it sits in the pipeline

Stainless is a verifier for a subset of Scala. Internally it lowers programs
through a chain of extraction phases. The default imperative pipeline
(`imperative/package.scala:42`) is:

```
EffectElaboration → AntiAliasing → ReturnElimination
                  → ImperativeCodeElimination → ImperativeCleanup
```

`AntiAliasing` is the heart of the imperative-to-functional translation. Its
job is to take a program that uses mutable objects (classes with `var` fields,
`Array[_]`, `MutableMap[_,_]`, etc.) and rewrite it into a purely functional
program *equivalent under the assumption that no two live names refer to the
same mutable cell*. Everything downstream (`ReturnElimination`,
`ImperativeCodeElimination`, etc.) assumes the program is alias-free.

To make that assumption safe, `AntiAliasing` simultaneously:

1. **Checks** the program for forbidden aliasing patterns and rejects them
   (via `MalformedStainlessCode` / `ImperativeEliminationException`).
2. **Rewrites** every function so that its side effects on parameters are
   returned as extra tuple components, and every call site is reshaped to
   thread the new values back through all known aliases.

The phase mixes in `EffectsAnalyzer`, `EffectsChecker` and `GhostChecker`. The
`EffectsAnalyzer` is the static analysis that powers everything below.

## 2. The model of memory

The semantics enforced by `AntiAliasing` are *value semantics* with controlled
sharing:

- An immutable type behaves as a pure value; copying it is free.
- A mutable type (= contains a `var` field reachable through its fields, or is
  `Array`, `MutableMap`, `AnyType`, etc. — see
  `SymbolOps.scala:88` `isMutableType`) is treated as if held by *one* name at
  a time. Multiple live names may *look at* the same object only through
  paths that the analyser can statically track. Anything the analyser cannot
  prove safe is rejected.

The phase represents what a variable refers to with three nested concepts
defined in `EffectsAnalyzer.scala`:

- `Accessor` — a single field/index step:
  `ADTFieldAccessor`, `ClassFieldAccessor`, `TupleFieldAccessor`,
  `ArrayAccessor(idx)`, `MutableMapAccessor(idx)`, `UnknownArrayAccessor`.
- `Path` — a sequence of accessors; supports `maybePrefixOf` /
  `definitelyPrefixOf` for aliasing reasoning.
- `Target(receiver: Variable, condition: Option[Expr], path: Path)` —
  "the cell reached from `receiver` through `path`, when `condition` holds".
  Conditions appear because a path may depend on an `if`/`match`
  (e.g. `val x = if (b) a1 else a2` gives two conditional targets).

Effects come in three kinds (`EffectsAnalyzer.scala:415`):

- `ReplacementEffect(receiver, path)` — `receiver.path` is fully overwritten
  (e.g. `r.lhs = newRef`).
- `ModifyingEffect(receiver, path)` — something *deeper* than `receiver.path`
  is mutated (e.g. `r.lhs.x = v`).
- `CombinedEffect` — both kinds at the same target.

The function `getTargets(expr, kind, path)` (`EffectsAnalyzer.scala:505`) is the
core: it answers *“after `var x = expr`, which receiver/path pairs does
mutation of `x` actually mutate?”*. When `getTargets` cannot answer precisely
it throws `MalformedStainlessCode`; the surrounding code uses that as a signal
to either fall back to a coarser strategy or to reject the program.

## 3. The transformation, at a glance

For every `FunDef` in the program, `extractFunction` (line 89) does:

1. `checkGhost(fd)` and `checkEffects(fd)` — see §5 for what the latter
   forbids.
2. Compute `aliasedParams` = parameters of `fd` that the function actually
   mutates (`getAliasedParams`, `EffectsAnalyzer.scala:148`).
3. Compute the new return type
   `getReturnType(fd) = tupleTypeWrap(originalReturn +: aliasedParams.map(_.tpe))`.
   I.e., a mutating function is rewritten to return its result *plus an
   updated copy of every parameter it mutates*.
4. Rewrite the body with `makeSideEffectsExplicit`, which walks the AST and
   turns every mutation into an assignment to a local `var` shadowing the
   parameter, and every call into an unpacking-and-rebinding sequence.

### 3.1 Signature rewrite

```scala
def modifyLhs(rr: RefRef, v: Int): Unit = { rr.lhs.x = v; rr.lhs.y = v }
```

becomes (sketch, line 341):

```scala
def modifyLhs(rr: RefRef, v: Int): (Unit, RefRef) =
  ((), RefRef(Ref(v, v), rr.rhs))
```

Inside the body, `rr` is shadowed by a fresh `var rr` initialised from the
parameter (`updateFunction`, lines 132–147). Every `rr.lhs.x = v` becomes
`rr = RefRef(Ref(v, rr.lhs.y), rr.rhs)` (functional copy update built by
`updatedTarget`, lines 1083–1160).

Postconditions are likewise rewritten: `old(rr)` is replaced with the
original parameter, `rr` in the post-condition refers to the relevant tuple
component of the new return value (lines 149–164).

### 3.2 Call-site rewrite

At a call `modifyLhs(testRR, 123)`, `mapApplication` (line 290) rewrites it
to:

```scala
val res = modifyLhs(testRR, 123)
testRR = res._2          // primary target assignment
// + assignments refreshing every known alias of testRR
res._1                   // the original return value
```

The interesting part is computing **which other names need refreshing**. The
environment carried during the walk is

```scala
type Environment = (Set[ValDef], Map[ValDef, Set[Target]], Map[Identifier, LocalFunDef])
```

i.e. for every binding of mutable type the phase remembers the set of
`Target`s it currently aliases (possibly conditional). After a call, any
binding whose target overlaps with what was modified is reassigned from the
freshly returned copy.

The phase distinguishes two regimes inside `mapApplication`:

- **Success regime** (line 401): if the argument's targets can be computed
  precisely (`ModifyingEffect(vd, Path.empty).on(arg)` succeeds), the call's
  effects can be lifted directly: assign the returned copy to the *primary
  targets* (the variables the arg aliases) and refresh their aliases.
- **Failure regime** (line 456): if precise targets cannot be computed for the
  argument (e.g. `modifyLhs(RefRef(lhsAlias, rhsAlias), 123)` where the
  constructed `RefRef` is fresh but its fields are aliases), the phase falls
  back to applying each *individual* effect of the callee on the argument
  expression. This rebuilds the receiver field-by-field rather than reusing
  the returned tuple component.

The comment block at lines 326–399 walks through both regimes on a worked
example; it is the most useful reading in the file.

### 3.3 Other constructs

- `Let(vd, e, b)` where `vd` is mutable (lines 712–833) is the trickiest
  case. See §4.
- `LetVar(vd, e, b)` where `vd` is mutable is *forbidden* by `EffectsChecker`
  (line 129) — a `var` is never allowed to hold a mutable object, only an
  immutable one. The transformation only sees `LetVar` of immutable type
  here.
- `FieldAssignment`, `ArrayUpdate`, `MutableMapUpdate`: become assignments to
  the *primary targets* obtained via `getDirectTargetsDealiased`, plus
  alias-refresh assignments (`updatedTargetsAndAliases`, line 645).
- `Swap` / `CellSwap`: rewritten to a temporary plus two updates on the two
  targets (lines 657–710). Both indices must be referentially transparent.
- `Lambda` (lines 877–905): captured mutable variables are *forbidden*
  (`"Illegal capturing of variables with mutable type"`); only the mutable
  *parameters* of the lambda may be modified. The lambda's body is rewritten
  in the same way as a function body (return tuple including updated mutable
  params).
- `FunctionType` / `PiType`: rewritten by `makeFunctionTypeExplicit`
  (line 51) so that the *type* of a higher-order parameter advertises the
  same tuple-of-updates return shape.

### 3.4 Pre-normalisation

Before `makeSideEffectsExplicit` runs, the body is pushed through the
`normalizer` object (lines 1285–1683). This normalisation is essential and
does several things:

- Hoists blocks out of expression positions
  (`f({stmt; e1}, {stmt; e2})` → `stmt; val e1' = e1; stmt; val e2' = e2; f(e1', e2')`).
- Binds non-referentially-transparent array/map indices to fresh vals so
  that the syntactic target `arr(i)` stays meaningful after `i` is mutated
  (line 1264–1275).
- Binds the receiver of an assignment when it is a non-trivial expression
  (`(if (cond) box1 else box2).value = 1234` →
  `val targetBound = if (cond) box1 else box2; targetBound.value = 1234`).
- For pattern matches, rebinds each pattern-bound mutable variable to a
  `scrut.asInstanceOf[C].fieldᵢ` so its target ties back to the scrutinee
  (lines 1438–1458).

Without this normalisation the target computation would have to handle far
more shapes; with it, the transformation deals with a much smaller surface.

## 4. The `Let` of mutable type — the most subtle case

`Let(vd, e, b)` where `vd: T` and `T` is mutable is where aliasing decisions
are concentrated (lines 712–833). The behaviour branches on whether
`getAllTargetsDealiased(e, env)` succeeds:

### 4.1 Targets computed precisely (`Some(targets)`)

This covers three sub-cases:

1. `e` is a *fresh* expression (e.g. `Ref(1, 2)`). `targets` is empty; the
   phase introduces a new abstract target `Target(vd, None, Path.empty)`
   meaning "vd points to a brand-new cell, distinct from every other live
   target".
2. `e` is a *precise alias* of one existing target (e.g. `val y = x` or
   `val y = a.left`). `targets` is a singleton with no condition; no new
   target is introduced — `vd` is registered as an *additional name for the
   same cell*. This is **allowed** aliasing.
3. `e` is a conditional mix (e.g. `if (cond) x else Ref(123)`). Each branch
   contributes a conditional target. If the conditions cover all cases
   (`disj` is provably true), `vd` is bound to those existing targets;
   otherwise an extra unconditional target is added for the fresh case
   (line 731–757). The phase records all of these as the alias set of `vd`.

After the body is transformed, `vd` becomes a `Let` if the body never
reassigns it (no `Assignment(vd, _)` was synthesised), or a `LetVar`
otherwise (line 764).

### 4.2 Targets could not be computed (`None`)

The fallback at line 767+ relies on a careful observation:

> If the (dealiased) set of mutable free variables of `e` and the set of
> mutable free variables of `b` are *disjoint*, then `b` cannot directly
> modify anything `e` referred to, and the binding is safe.

The check is refined: `e`'s variables are taken only at *terminal* positions
(`terminalVarsOfExprDealiased`, lines 1016–1052) — the locations whose value
actually constitutes the result of `e` — because non-terminal mutations are
handled by the recursive rewrite anyway.

- If the sets are disjoint, the let is allowed; effects of `b` on `vd` are
  copied back onto `e` (`copyEffects`, lines 791–795), preserving observable
  mutations of the underlying cell.
- If they overlap, the program is rejected with:

  ```
  Unsupported `val` definition in AntiAliasing
  The following variables of mutable types are shared between the binding
  and the body: ...
  ```

  An example is `IllegalAliasing4.scala` in
  `frontends/benchmarks/extraction/invalid/`: a `val b = { if (n > 0) {
  createA(n, alias); B(alias) } else B(A(0)) }` cannot be analysed because
  `alias` (≡ `counter`) appears both as a target of `b` *and* in the body
  outside `b`, and the precise targets of the if-expression cannot be
  reconstructed.

## 5. The rules: what aliasing is allowed and what is not

The combined verdict of `EffectsChecker` and the in-body checks of
`AntiAliasing` define Stainless's aliasing discipline.

### 5.1 Aliasing that is allowed

1. **Aliases through value bindings of immutable type.** Anything happens at
   the value level — they are just copies.
2. **`val` aliases of mutable objects, when targets are statically traceable.**
   `val a = x.left` is fine: `a` is recorded as an alias of `x.left`; any
   later mutation through `a.foo = ...` is rewritten to update *both* `a` and
   `x.left` (alias refresh). See `TargetMutation9` in
   `frontends/benchmarks/imperative/valid/`.
3. **Passing a mutable parameter that is then mutated.** The parameter is
   thread-rebound and the caller is rewritten to receive the updated copy.
4. **Multiple `val` aliases sharing *disjoint* paths into the same root.**
   `val lhs = rr.lhs; val rhs = rr.rhs` is fine because the two paths
   `.lhs` and `.rhs` are not prefixes of each other. The targets are
   tracked independently.
5. **Conditional aliases**, as long as the alternatives can be expressed as a
   set of conditional targets — `val y = if (b) a1 else a2` and then
   `y.x = 42` is allowed and is rewritten to two conditional assignments to
   `a1` and `a2`. (Compare `IllegalAliasing3.scala` — same shape with `var`
   is rejected.)
6. **Aliases inside a freshly-constructed object whose components have
   disjoint targets.** `g(a)` where `g` reassigns `a.left.c.x` is fine even
   though the rebuilt `A(...)` for `a` reuses subterms of `a` — see the
   worked examples in `imperative/valid/i1051a.scala` and `i1051b.scala`.

### 5.2 Aliasing that is rejected

The errors below are raised either from `EffectsChecker` (statically, before
the rewrite) or from `AntiAliasing` itself (during rewrite when targets
cannot be computed).

1. **Binding a mutable expression to a `var`.**
   ```
   Cannot bind expression of a mutable type to a `var`
   ```
   (`EffectsChecker.scala:130`; example: `IllegalAliasing3.scala`)
   Rationale: assignment to a `var` of mutable type would create unbounded
   aliasing the phase cannot track.

2. **Aliased arguments at a call site.**
   ```
   Illegal passing of aliased parameters
   ```
   (`AntiAliasing.scala:546–558`, `checkAliasing`; examples:
   `ArgumentAliasing.scala`, `IllegalAliasing2.scala`, `AliasedFreshExpr.scala`)
   Two arguments to the same call (or to an ADT/class/tuple constructor,
   array literal, `ArrayUpdated`, `MapUpdated`) may not have overlapping
   targets (`target1.maybePrefixOf(target2) || target2.maybePrefixOf(target1)`).
   This includes a constructor passed `(c1, c1)` — even though
   `Trout(c1, c1)` is technically a fresh ADT, the result is an aliasing
   trap and is rejected.

3. **Updating a field/array slot/map entry of mutable element type with a
   non-fresh expression.**
   ```
   Cannot update a field whose type (T) is mutable with a non-fresh
   expression
   ```
   (`EffectsChecker.scala:135–158`; examples: `BadAliasing1/2/3.scala`)
   Storing a *named* mutable object into a structure would create a path
   alias the analyser cannot follow. Only freshly constructed (=
   `isExpressionFresh`, `EffectsAnalyzer.scala:689`) values may be stored.

4. **`val v = e` of mutable type where `e`'s and `b`'s mutable variables
   overlap and `e`'s targets cannot be computed.**
   ```
   Illegal aliasing: e
   Hint: this error occurs due to:
     -the type of v (T) being mutable
     -the definition of v not being fresh
     -the definition of v containing variables of mutable types that also
      appear after the declaration of v
   ```
   (`EffectsChecker.scala:107`; example: `IllegalAliasing.scala`)
   The wider variant, raised later when the same shape survives extraction:
   ```
   Unsupported `val` definition in AntiAliasing
   ```
   (`AntiAliasing.scala:828`; example: `IllegalAliasing4.scala`,
   `MapAliasing1/2.scala`).

5. **Capturing a mutable variable in a lambda.**
   ```
   Illegal capturing of variables with mutable type
   ```
   (`AntiAliasing.scala:887`)
   A lambda may only mutate its own (mutable) parameters, never captured
   state. Lambdas with mutable return types must return a fresh value
   (`EffectsChecker.scala:165`).

6. **Inner / recursive functions returning non-fresh results.**
   ```
   Illegal recursive functions returning non-fresh result
   ```
   (`EffectsChecker.scala:47`)
   Returning a non-fresh mutable value from a recursive or `LetRec`
   function would let the result alias an argument; the phase relies on
   non-recursive direct-callee inlining (`getTargets` for
   `FunctionInvocation`, `EffectsAnalyzer.scala:584`) to track this, which is
   only sound for non-recursive callees.

7. **Passing an inner-fun argument that aliases one of its captures.**
   ```
   Illegal passing of aliased local variable
   ```
   (`AntiAliasing.scala:945`)
   An inner function closes over its free mutable vars; passing one of
   those (or anything aliasing it) as an argument would conflict with the
   capture.

8. **Type-parameter mutability discipline.**
   Instantiating a type parameter that is *not* declared `@mutable` with a
   mutable type is rejected (`EffectsChecker.scala:52–69`). Likewise:
   - `Set[T]` and `Bag[T]` with mutable `T`;
   - `Map[K, _]` and `MutableMap[K, _]` with mutable `K`;
   - `MutableMap[_, V]` with mutable `V` for `updated`/`duplicate`.
   These reflect the fact that those collections rely on structural equality
   and copying that mutable types do not support.

9. **Effects in disallowed locations.** `checkEffectsLocations`
   (`EffectsChecker.scala:245`) forbids side effects in `require`/`ensuring`/
   `decreases`/`assert`/`assume`, in `forall` predicates, in invariants, in
   pattern guards, in `&&`/`||`/`==>` operands (because they short-circuit),
   in `Old(...)`, and in the `default` of `Array.fill`. A `@pure` or
   `@invariant` function is rejected if it has any effect.

10. **Calling a synthetic helper on a class with mutable fields.** Auto-generated
    `equals`/`hashCode`-style methods (`isMutableSynthetic`,
    `EffectsChecker.scala:22`) can't be analysed and are rejected at call
    sites:
    ```
    Cannot call '...' on a class with mutable fields
    ```

11. **Ambiguous combined effect on a non-empty path** —
    `EffectsAnalyzer.scala:454` — raised when an effect of `CombinedKind`
    would apply at a path that the analyser cannot prove distinguishable
    from the path that produced it.

12. **`ArrayUpdated` / `MapUpdated` with effectful sub-expressions** —
    `EffectsChecker.scala:273–282` — the copy-update primitives must be
    pure in their arguments.

## 6. Why the phase is fragile

A few structural reasons that the source acknowledges explicitly:

- `getTargets` is defined on *pre-transformation* trees only. Any code path
  that would need targets of an expression *after* the rewrite (in particular,
  function applications producing the augmented tuple) must work around
  this. The `Let` case at line 712 specifically introduces a `LetVar` for
  mutable return types to avoid the trap; the long comment at lines 279–289
  describes the problem and the partial workaround.
- The success/failure dichotomy of `mapApplication` (lines 401 vs 456) means
  the *same* program can be rewritten in two very different shapes depending
  on whether the argument's targets happen to be computable. The lengthy
  comments at lines 326–466 record the worked examples
  (`test1`/`test2`/`t3`/`replaceLhs`) that motivate the two paths.
- The `Let`-of-mutable case (§4) silently splits into "precise" and "best
  effort with disjointness check"; the failure mode in the second branch
  surfaces as `Unsupported val definition in AntiAliasing`, which is often
  reported as a user-visible bug because the same code would be accepted
  after a tiny syntactic change.
- `simplifyOr` (lines 1169–1237) and the condition tracking for if-branches
  feed into target equality; missed simplifications can cascade into
  spurious "could not compute precise targets" errors.
- `normalizer` (lines 1285–1683) is doing a lot of work to make the AST
  uniform before the rewrite. Bugs in normalisation manifest as missing
  binders or stale targets later.

Together, these mean a small change to the transformation has to be
validated against essentially every benchmark in
`frontends/benchmarks/imperative/{valid,invalid}` and the matching ones
under `frontends/benchmarks/extraction/invalid/` — which is the *de facto*
specification of the discipline described in §5.

## 7. Pointers to the most useful reading

| Question                                                      | Where to look                                                |
| ------------------------------------------------------------- | ------------------------------------------------------------ |
| What is "mutable"?                                            | `SymbolOps.scala:48` `isMutableType`                         |
| What is "fresh"?                                              | `EffectsAnalyzer.scala:689` `isExpressionFresh`              |
| How are targets computed?                                     | `EffectsAnalyzer.scala:505` `getTargets`                     |
| What does the function signature become?                      | `EffectsAnalyzer.scala:153` `getReturnType`                  |
| How is a call site rewritten?                                 | `AntiAliasing.scala:290` `mapApplication`                    |
| How is `val x = …` of mutable type rewritten?                 | `AntiAliasing.scala:712`                                     |
| How are aliases refreshed after an effect?                    | `AntiAliasing.scala:634` `updatedAliasingValDefs`            |
| How is a functional copy with a path update built?            | `AntiAliasing.scala:1083` `updatedTarget`                    |
| What gets normalised before the transformation?               | `AntiAliasing.scala:1285` `normalizer`                       |
| What does the checker forbid?                                 | `EffectsChecker.scala:40` `check`                            |
| Working examples (one comment block, many cases)              | `AntiAliasing.scala:326`–`466`                               |
| Benchmarks acting as the spec for §5.1 (allowed)              | `frontends/benchmarks/imperative/valid/{TargetMutation*,i1051*,OpaqueMutation1,Sequencing9,Issue1097,ClassReconstruction}.scala` |
| Benchmarks acting as the spec for §5.2 (rejected)             | `frontends/benchmarks/extraction/invalid/{BadAliasing*,IllegalAliasing*,ArgumentAliasing,AliasedFreshExpr,MapAliasing*}.scala` and `frontends/benchmarks/imperative/invalid/i916*.scala` |
