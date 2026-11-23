# Stainless semantics

This file defines what the expressions of Stainless's last tree layer
(`stainless.ast`, the trees that `extraction.pipeline` produces) mean, as an
extension of [Inox's semantics](../inox/proofs/semantics.md). Every Inox
expression keeps its meaning; this file adds the expressions that Stainless
has and Inox doesn't.

It is the first layer of a semantics per tree layer, each extending the one
below as the trees do, so that each phase of the extraction can be stated to
preserve meaning. The statement for `InoxEncoder`, the last step into Inox, is
tested by `EncoderSemanticsSuite` (see [README.md](README.md)).

This version covers contracts (`require`, `ensuring`, `assert`), pattern
matching on constructors, tuples and literals, with guards, and the JVM's
division and remainder on `BigInt`. It doesn't cover arrays, `choose`,
`@extern`, other patterns or Stainless's types yet.

```inox-sem
(import "../inox/proofs/semantics.md")
```

## Failures

A run that violates a contract gets stuck, as a run where an Inox `assume`
doesn't hold does: a precondition, a postcondition or an assertion that
doesn't hold, a match that no case matches, and a division by zero. Type
checking and the VCs rule all of these out. What they don't rule out is the
trusted base: the `assume`s and the contracts of `@extern` functions. So a
verified program never gets stuck where its trusted assumptions hold.

## Expressions

The expressions of `stainless.ast.Expressions` in this fragment, with the
fields that evaluation uses. `Ensuring` holds the parameter `res` and body
`post` of its postcondition's lambda.

Stainless's `Division` and `Remainder` on `BigInt` are the JVM's, which round
toward zero, while Inox's are euclidean. The two trees are the same in
Stainless, so `JVMDivision` and `JVMRemainder` stand for them on integers: the
translation from Stainless's trees picks them by the type of the operands.

```inox-sem
(extend-datatype Expr
  (Require (pred Expr) (body Expr))
  (Ensuring (body Expr) (res Id) (post Expr))
  (Assert (pred Expr) (body Expr))
  (MatchExpr (scrutinee Expr) (cases (List MatchCase)))
  (JVMDivision (lhs Expr) (rhs Expr))
  (JVMRemainder (lhs Expr) (rhs Expr)))

(datatype MatchCase
  (MatchCase (pattern Pattern) (guard (Option Expr)) (rhs Expr)))

(datatype Pattern
  (WildcardPattern (binder (Option Id)))
  (ADTPattern (binder (Option Id)) (id Id) (subs (List Pattern)))
  (TuplePattern (binder (Option Id)) (subs (List Pattern)))
  (LiteralPattern (binder (Option Id)) (lit Expr)))
```

## Contracts

A precondition gets stuck when it doesn't hold, whoever calls the function: the
statement about a program assumes that the entry point's own precondition
holds, and every other call is checked. A postcondition is checked on the
value of the body, and an assertion before its body.

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
```

## Pattern matching

The cases are tried in order. A case applies when its pattern matches the
scrutinee and its guard, evaluated with the pattern's bindings, holds. A match
that no case applies to gets stuck. Matching a pattern evaluates the literals it
compares with, and gives the bindings of its binders, or `None` if the value
doesn't match.

```inox-sem
(case eval (MatchExpr scrutinee cases)
  (let! ((v (eval P fuel env scrutinee)))
    (eval-cases P fuel env v cases)))

(define (eval-cases (P Program) (fuel Int) (env Env) (v Value) (cases (List MatchCase))) (Result Value)
  (match cases
    ((Nil) (Stuck))
    ((Cons (MatchCase pat guard rhs) rest)
      (let! ((m (match-pattern P fuel env v pat)))
        (match m
          ((None) (eval-cases P fuel env v rest))
          ((Some bs)
            (match env
              ((Env tys vars)
                (let ((inner (Env tys (append-env bs vars))))
                  (match guard
                    ((None) (eval P fuel inner rhs))
                    ((Some g)
                      (let! ((b (eval-bool P fuel inner g)))
                        (if b (eval P fuel inner rhs) (eval-cases P fuel env v rest))))))))))))))

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
        (if same (Ok (Some (bind-binder b v (Nil)))) (Ok (None)))))))

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
```

## Integer division

On the JVM, `BigInt`'s `/` rounds toward zero and `%` has the sign of the
dividend; both get stuck on a zero divisor. On other operands, they are Inox's.

```inox-sem
(case eval (JVMDivision lhs rhs)
  (let! ((a (eval P fuel env lhs)) (b (eval P fuel env rhs)))
    (match a
      ((IntV x)
        (match b
          ((IntV y) (if (= y 0) (Stuck) (Ok (IntV (tdiv x y)))))
          (_ (Stuck))))
      (_ (arith-div a b)))))

(case eval (JVMRemainder lhs rhs)
  (let! ((a (eval P fuel env lhs)) (b (eval P fuel env rhs)))
    (match a
      ((IntV x)
        (match b
          ((IntV y) (if (= y 0) (Stuck) (Ok (IntV (trem x y)))))
          (_ (Stuck))))
      (_ (arith-rem a b)))))
```
