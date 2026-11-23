# Stainless semantics

This file defines what the trees of Stainless's last layer (`stainless.ast`,
the trees that `extraction.pipeline` produces) mean, as an extension of
[Inox's semantics](../inox/proofs/semantics.md). Every Inox expression keeps
its meaning; this file adds the expressions, patterns, values and types that
Stainless has and Inox doesn't.

It is the first layer of a semantics per tree layer, each extending the one
below as the trees do, so that each phase of the extraction can be stated to
preserve meaning. The statement for `InoxEncoder`, the last step into Inox, is
tested by `EncoderSemanticsSuite` (see [README.md](README.md)).

```inox-sem
(import "../inox/proofs/semantics.md")
```

## Failures

A run that violates a contract gets stuck, as a run where an Inox `assume`
doesn't hold does: a precondition, a postcondition or an assertion that
doesn't hold, a match that no case matches, a division by zero, an array index
out of bounds, a `choose` whose predicate the chosen value doesn't satisfy,
and an `error`. Type checking and the VCs rule all of these out. What they
don't rule out is the trusted base: the `assume`s and the contracts of
`@extern` functions, whose bodies are `choose`s of their postconditions. So a
verified program never gets stuck where its trusted assumptions hold.

## Trees

The trees of `stainless.ast.Expressions` and `stainless.ast.Types`, with the
fields that evaluation uses.

- `Ensuring` holds the parameter `res` and body `post` of its postcondition's
  lambda, and `RefinementPattern` those of its predicate.
- Stainless's `Division` and `Remainder` on `BigInt` and on bit-vectors are
  the JVM's: on `BigInt`, they round toward zero, while Inox's are euclidean,
  and on bit-vectors, they fail on a zero divisor, where Inox's are defined.
  The trees are the same in Stainless and in Inox, so `JVMDivision` and
  `JVMRemainder` stand for them: the translation from Stainless's trees picks
  them by the type of the operands.
- An `UnapplyPattern` holds the `isEmpty` and `get` accessors of its `unapply`
  function, with their type arguments, which Stainless finds from the
  function's flags and types.
- A `LargeArray` holds its elements in order of their indices.
- `Annotated` and `Decreases` keep only what evaluation uses: the body.
- `NoTree` stands for an expression that has no meaning, `Choose` for a value
  that a model gives (see below), and `SizedADT` is a constructor applied to
  its arguments, with a size that only termination checking uses.

`RecursiveType`, `ValueType` and `AnnotatedType` are types for the type
checker: a value has them when it has the type they wrap, an ADT type for
`RecursiveType`. The translation into the semantics replaces them with it.

```inox-sem
(extend-datatype Expr
  (NoTree)
  (Choose (res Id) (tps (List Type)) (tpe Type) (pred Expr))
  (Require (pred Expr) (body Expr))
  (Annotated (body Expr))
  (Ensuring (body Expr) (res Id) (post Expr))
  (Assert (pred Expr) (body Expr))
  (MatchExpr (scrutinee Expr) (cases (List MatchCase)))
  (Passes (in Expr) (out Expr) (cases (List MatchCase)))
  (JVMDivision (lhs Expr) (rhs Expr))
  (JVMRemainder (lhs Expr) (rhs Expr))
  (JVMShiftLeft (lhs Expr) (rhs Expr))
  (JVMAShiftRight (lhs Expr) (rhs Expr))
  (JVMLShiftRight (lhs Expr) (rhs Expr))
  (FiniteArray (elems (List Expr)))
  (LargeArray (elems (List ArrayEntry)) (default Expr) (size Expr))
  (ArraySelect (array Expr) (index Expr))
  (ArrayUpdated (array Expr) (index Expr) (value Expr))
  (ArrayLength (array Expr))
  (Decreases (body Expr))
  (Max (exprs (List Expr)))
  (SizedADT (id Id) (tps (List Type)) (args (List Expr)) (size Expr)))

(datatype ArrayEntry
  (ArrayEntry (index Int) (value Expr)))

(datatype MatchCase
  (MatchCase (pattern Pattern) (guard (Option Expr)) (rhs Expr)))

(datatype Pattern
  (WildcardPattern (binder (Option Id)))
  (ADTPattern (binder (Option Id)) (id Id) (subs (List Pattern)))
  (TuplePattern (binder (Option Id)) (subs (List Pattern)))
  (LiteralPattern (binder (Option Id)) (lit Expr))
  (AlternativePattern (binder (Option Id)) (subs (List Pattern)))
  (RefinementPattern (underlying Pattern) (param Id) (pred Expr))
  (UnapplyPattern (binder (Option Id)) (recs (List Expr)) (id Id) (tps (List Type))
    (is-empty Id) (is-empty-tps (List Type)) (get Id) (get-tps (List Type)) (subs (List Pattern))))

(extend-datatype Type
  (ArrayType (base Type)))

(extend-datatype Value
  (ArrayV (elems (List Value))))
```

## Contracts

A precondition gets stuck when it doesn't hold, whoever calls the function: the
statement about a program assumes that the entry point's own precondition
holds, and every other call is checked. A postcondition is checked on the
value of the body, and an assertion before its body. `Annotated` and
`Decreases` mean their bodies: the measure of `Decreases` is checked by
termination, not by evaluation.

```inox-sem
(case eval (Require pred body)
  (let! ((b (eval-bool P fuel env pred)))
    (if b (eval P fuel env body) (Stuck))))

(case eval (Ensuring body res post)
  (let! ((v (eval P fuel env body))
         (b (eval-bool P fuel (env-bind env res v) post)))
    (if b (Ok v) (Stuck))))

(case eval (Assert pred body)
  (let! ((b (eval-bool P fuel env pred)))
    (if b (eval P fuel env body) (Stuck))))

(case eval (Annotated body)
  (eval P fuel env body))

(case eval (Decreases body)
  (eval P fuel env body))

(case eval (NoTree)
  (Stuck))
```

## Choices

A `choose` is a value that a model gives, as it gives the uninterpreted
functions: the model has an interpretation named by the `choose`'s `res`, at
the types `tps` that the value depends on, whose parameters name the
variables that the value depends on. Its body is evaluated with them bound to
their values, as the body of an uninterpreted function is, with a step of
fuel. The value must have the `choose`'s type and satisfy its predicate,
which the model is chosen to ensure wherever a value does; otherwise the run
gets stuck.

The type arguments of a `choose` are those of its function when it is a
function's body, and otherwise those that its type refers to, as
`InoxEncoder` makes them.

```inox-sem
(define (lookup-vars (vars (List Binding)) (ids (List Id))) (Result (List Binding))
  (match ids
    ((Nil) (Ok (Nil)))
    ((Cons x rest)
      (let! ((v (lookup-var vars x))
             (bs (lookup-vars vars rest)))
        (Ok (Cons (Binding x v) bs))))))

(case eval (Choose res tps tpe pred)
  (if (<= fuel 0)
    (OutOfFuel)
    (match P
      ((Program _ _ _ is _)
        (let! ((i (lookup-interpretation is res (resolve-all (env-types env) tps))))
          (match i
            ((Interpretation _ _ params body)
              (let! ((bs (lookup-vars (env-vars env) params))
                     (v (eval P (- fuel 1) (Env (Nil) bs) body))
                     (b (eval-bool P fuel (env-bind env res v) pred)))
                (if (and b (has-type P env v tpe)) (Ok v) (Stuck))))))))))
```

## Pattern matching

The cases are tried in order. A case applies when its pattern matches the
scrutinee and its guard, evaluated with the pattern's bindings, holds. A match
that no case applies to gets stuck. Matching a pattern evaluates the
expressions it holds, and gives the bindings of its binders, or `None` if the
value doesn't match.

- An alternative pattern matches when one of its alternatives does, and binds
  only its own binder, as Scala's alternatives have none.
- A refinement pattern matches when its underlying pattern does and its
  predicate holds for the value, with the underlying pattern's bindings.
- An unapply pattern calls its `unapply` function on its receivers and the
  value, and doesn't match when `isEmpty` holds of the result. Otherwise its
  subpatterns match the result of `get`: the whole result for one subpattern,
  and its elements, a tuple, for several.

`Passes` holds when `out` is the result of matching `in` against its cases,
with `out` itself when none applies.

```inox-sem
(case eval (MatchExpr scrutinee cases)
  (let! ((v (eval P fuel env scrutinee)))
    (eval-cases P fuel env v cases (Stuck))))

(case eval (Passes in out cases)
  (let! ((o (eval P fuel env out))
         (v (eval P fuel env in))
         (r (eval-cases P fuel env v cases (Ok o)))
         (same (value-eq P o r)))
    (Ok (BoolV same))))

(define (eval-cases (P Program) (fuel Int) (env Env) (v Value) (cases (List MatchCase)) (none (Result Value))) (Result Value)
  (match cases
    ((Nil) none)
    ((Cons (MatchCase pat guard rhs) rest)
      (let! ((m (match-pattern P fuel env v pat)))
        (match m
          ((None) (eval-cases P fuel env v rest none))
          ((Some bs)
            (match env
              ((Env tys vars)
                (let ((inner (Env tys (append-env bs vars))))
                  (match guard
                    ((None) (eval P fuel inner rhs))
                    ((Some g)
                      (let! ((b (eval-bool P fuel inner g)))
                        (if b (eval P fuel inner rhs) (eval-cases P fuel env v rest none))))))))))))))

(define (bind-binder (b (Option Id)) (v Value) (bs (List Binding))) (List Binding)
  (match b
    ((None) bs)
    ((Some x) (Cons (Binding x v) bs))))

(define (add-binder (b (Option Id)) (v Value) (m (Option (List Binding)))) (Option (List Binding))
  (match m
    ((None) (None))
    ((Some bs) (Some (bind-binder b v bs)))))

(define (match-pattern (P Program) (fuel Int) (env Env) (v Value) (p Pattern)) (Result (Option (List Binding)))
  (match p
    ((WildcardPattern b) (Ok (Some (bind-binder b v (Nil)))))
    ((ADTPattern b c subs)
      (match v
        ((ADTV d vs)
          (if (= c d)
            (let! ((m (match-patterns P fuel env vs subs)))
              (Ok (add-binder b v m)))
            (Ok (None))))
        (_ (Stuck))))
    ((TuplePattern b subs)
      (match v
        ((TupleV vs)
          (let! ((m (match-patterns P fuel env vs subs)))
            (Ok (add-binder b v m))))
        (_ (Stuck))))
    ((LiteralPattern b lit)
      (let! ((l (eval P fuel env lit))
             (same (value-eq P v l)))
        (if same (Ok (Some (bind-binder b v (Nil)))) (Ok (None)))))
    ((AlternativePattern b subs)
      (let! ((any (match-any P fuel env v subs)))
        (if any (Ok (Some (bind-binder b v (Nil)))) (Ok (None)))))
    ((RefinementPattern under x pred)
      (let! ((m (match-pattern P fuel env v under)))
        (match m
          ((None) (Ok (None)))
          ((Some bs)
            (let! ((b (eval-bool P fuel (env-bind env x v) pred)))
              (if b (Ok (Some bs)) (Ok (None))))))))
    ((UnapplyPattern b recs f tps is-empty is-empty-tps get get-tps subs)
      (let! ((rs (eval-list P fuel env recs))
             (u (call P fuel f tps (env-types env) (append-values rs (Cons v (Nil)))))
             (e (call P fuel is-empty is-empty-tps (env-types env) (Cons u (Nil)))))
        (match e
          ((BoolV true) (Ok (None)))
          ((BoolV false)
            (let! ((g (call P fuel get get-tps (env-types env) (Cons u (Nil))))
                   (m (match-patterns P fuel env (unapplied g (patterns-length subs)) subs)))
              (Ok (add-binder b v m))))
          (_ (Stuck)))))))

;; the values that the subpatterns of an extractor match: the result of `get`
;; for one, and the elements of the tuple it is for several
(define (unapplied (g Value) (n Int)) (List Value)
  (if (= n 1)
    (Cons g (Nil))
    (match g
      ((TupleV vs) vs)
      (_ (Nil)))))

(define (patterns-length (ps (List Pattern))) Int
  (match ps
    ((Nil) 0)
    ((Cons _ rest) (+ 1 (patterns-length rest)))))

(define (match-any (P Program) (fuel Int) (env Env) (v Value) (ps (List Pattern))) (Result Bool)
  (match ps
    ((Nil) (Ok false))
    ((Cons p rest)
      (let! ((m (match-pattern P fuel env v p)))
        (match m
          ((None) (match-any P fuel env v rest))
          ((Some _) (Ok true)))))))

(define (match-patterns (P Program) (fuel Int) (env Env) (vs (List Value)) (ps (List Pattern))) (Result (Option (List Binding)))
  (match ps
    ((Nil)
      (match vs
        ((Nil) (Ok (Some (Nil))))
        (_ (Stuck))))
    ((Cons p rest)
      (match vs
        ((Nil) (Stuck))
        ((Cons v others)
          (let! ((m (match-pattern P fuel env v p)))
            (match m
              ((None) (Ok (None)))
              ((Some bs)
                (let! ((n (match-patterns P fuel env others rest)))
                  (match n
                    ((None) (Ok (None)))
                    ((Some cs) (Ok (Some (append-env bs cs))))))))))))))

(define (append-values (xs (List Value)) (ys (List Value))) (List Value)
  (match xs
    ((Nil) ys)
    ((Cons x rest) (Cons x (append-values rest ys)))))
```

## Integer division

On the JVM, `BigInt`'s `/` rounds toward zero and `%` has the sign of the
dividend. Both get stuck on a zero divisor, on `BigInt`s and on bit-vectors,
which otherwise divide as Inox's do.

```inox-sem
(case eval (JVMDivision lhs rhs)
  (let! ((a (eval P fuel env lhs)) (b (eval P fuel env rhs)))
    (if (zero-divisor b)
      (Stuck)
      (match a
        ((IntV x)
          (match b
            ((IntV y) (Ok (IntV (tdiv x y))))
            (_ (Stuck))))
        (_ (arith-div a b))))))

(case eval (JVMRemainder lhs rhs)
  (let! ((a (eval P fuel env lhs)) (b (eval P fuel env rhs)))
    (if (zero-divisor b)
      (Stuck)
      (match a
        ((IntV x)
          (match b
            ((IntV y) (Ok (IntV (trem x y))))
            (_ (Stuck))))
        (_ (arith-rem a b))))))

(define (zero-divisor (b Value)) Bool
  (match b
    ((IntV y) (= y 0))
    ((BVV _ _ y) (= y 0))
    (_ false)))
```

## Shifts

The JVM's shifts on `Int`s and `Long`s take the amount modulo the width, so
`1 << 33` is `2`. Inox's, from SMT-LIB, shift everything out instead. Both
agree on amounts from `0` to the width.

```inox-sem
(define (jvm-shift (op BitOp) (a Value) (b Value)) (Result Value)
  (match a
    ((BVV s w x)
      (match b
        ((BVV t v y) (if (same-bv s w t v) (Ok (bit-op op s w x (mod y w))) (Stuck)))
        (_ (Stuck))))
    (_ (Stuck))))

(case eval (JVMShiftLeft lhs rhs)
  (let! ((a (eval P fuel env lhs)) (b (eval P fuel env rhs)))
    (jvm-shift (ShiftLeftOp) a b)))

(case eval (JVMAShiftRight lhs rhs)
  (let! ((a (eval P fuel env lhs)) (b (eval P fuel env rhs)))
    (jvm-shift (AShiftRightOp) a b)))

(case eval (JVMLShiftRight lhs rhs)
  (let! ((a (eval P fuel env lhs)) (b (eval P fuel env rhs)))
    (jvm-shift (LShiftRightOp) a b)))
```

## Arrays

An array is a value that holds its elements, indexed from `0` by `Int`s. At
this layer, arrays are values: updating one gives a new array. Reading or
updating out of bounds gets stuck, as does a negative size. Two arrays are
equal when their elements are, and a value of `(ArrayType base)` is an array
of fewer than `2^31` values of `base`.

```inox-sem
(case eval (FiniteArray elems)
  (let! ((vs (eval-list P fuel env elems)))
    (Ok (ArrayV vs))))

(case eval (LargeArray elems default size)
  (let! ((es (eval-entries P fuel env elems))
         (d (eval P fuel env default))
         (n (eval-index P fuel env size)))
    (if (< n 0) (Stuck) (Ok (ArrayV (array-fill 0 n d es))))))

(case eval (ArraySelect array index)
  (let! ((vs (eval-array P fuel env array))
         (i (eval-index P fuel env index)))
    (array-get vs i)))

(case eval (ArrayUpdated array index value)
  (let! ((vs (eval-array P fuel env array))
         (i (eval-index P fuel env index))
         (v (eval P fuel env value))
         (ws (array-set vs i v)))
    (Ok (ArrayV ws))))

(case eval (ArrayLength array)
  (let! ((vs (eval-array P fuel env array)))
    (Ok (bv true 32 (values-length vs)))))

(define (eval-array (P Program) (fuel Int) (env Env) (e Expr)) (Result (List Value))
  (let! ((a (eval P fuel env e)))
    (match a
      ((ArrayV vs) (Ok vs))
      (_ (Stuck)))))

(define (eval-index (P Program) (fuel Int) (env Env) (e Expr)) (Result Int)
  (let! ((a (eval P fuel env e)))
    (match a
      ((BVV s w x) (Ok (bv-int s w x)))
      (_ (Stuck)))))

(datatype ArrayEntryValue
  (ArrayEntryValue (index Int) (value Value)))

(define (eval-entries (P Program) (fuel Int) (env Env) (es (List ArrayEntry))) (Result (List ArrayEntryValue))
  (match es
    ((Nil) (Ok (Nil)))
    ((Cons (ArrayEntry i e) rest)
      (let! ((v (eval P fuel env e))
             (vs (eval-entries P fuel env rest)))
        (Ok (Cons (ArrayEntryValue i v) vs))))))

(define (entry-at (es (List ArrayEntryValue)) (i Int) (d Value)) Value
  (match es
    ((Nil) d)
    ((Cons (ArrayEntryValue j v) rest) (if (= i j) v (entry-at rest i d)))))

(define (array-fill (i Int) (n Int) (d Value) (es (List ArrayEntryValue))) (List Value)
  (if (<= n i)
    (Nil)
    (Cons (entry-at es i d) (array-fill (+ i 1) n d es))))

(define (array-get (vs (List Value)) (i Int)) (Result Value)
  (match vs
    ((Nil) (Stuck))
    ((Cons v rest) (if (= i 0) (Ok v) (array-get rest (- i 1))))))

(define (array-set (vs (List Value)) (i Int) (v Value)) (Result (List Value))
  (match vs
    ((Nil) (Stuck))
    ((Cons w rest)
      (if (= i 0)
        (Ok (Cons v rest))
        (let! ((ws (array-set rest (- i 1) v)))
          (Ok (Cons w ws)))))))

(define (values-length (vs (List Value))) Int
  (match vs
    ((Nil) 0)
    ((Cons _ rest) (+ 1 (values-length rest)))))

(case value-eq (ArrayV xs)
  (match b
    ((ArrayV ys) (values-eq P xs ys))
    (_ (Ok false))))

(case has-type (ArrayType base)
  (match v
    ((ArrayV vs) (and (all-have-type P env vs base) (< (values-length vs) (pow2 31))))
    (_ false)))
```

## Other expressions

`Max` is the largest of its integers. A `SizedADT` is the constructor
applied to its arguments, as `ADT`, after evaluating its size.

```inox-sem
(case eval (Max exprs)
  (let! ((vs (eval-list P fuel env exprs)))
    (int-max vs)))

(define (int-max (vs (List Value))) (Result Value)
  (match vs
    ((Cons (IntV x) (Nil)) (Ok (IntV x)))
    ((Cons (IntV x) rest)
      (let! ((m (int-max rest)))
        (match m
          ((IntV y) (Ok (IntV (if (< x y) y x))))
          (_ (Stuck)))))
    (_ (Stuck))))

(case eval (SizedADT c tps args size)
  (let! ((vs (eval-list P fuel env args))
         (n (eval P fuel env size)))
    (construct P fuel env c tps vs)))
```
