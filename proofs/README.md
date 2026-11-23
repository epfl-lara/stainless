# Semantics of Stainless's trees

[`semantics.md`](semantics.md) defines what the trees of Stainless's last
layer, `stainless.ast`, mean, as an extension of
[Inox's semantics](../inox/proofs/semantics.md): it imports Inox's file and
adds the expressions, patterns, values and types that Stainless has and Inox
doesn't. These are contracts, pattern matching with all of Stainless's
patterns, `passes`, `choose`, arrays, the JVM's division and shifts, `max`, and
sized constructors. A run that violates a contract gets stuck, as one where an
`assume` doesn't hold does. Verification rules out the first, and the second
is the trusted base. Inox's expressions keep their meaning. The goal is a
semantics per tree layer, each extending the one below as the trees do, so
that each extraction phase can be stated, tested and then proved in Lean to
preserve meaning.

`EncoderSemanticsSuite` tests `InoxEncoder`, the last step into Inox. It runs
on the functions of some verification benchmarks, of a sample with negative
divisions and violated contracts, and of a sample with arrays, shifts,
extractors, alternatives, `passes` and `choose`. It compares the program that
the extraction produces, under Stainless's semantics, with the program that
`InoxEncoder` makes of it, under Inox's, on random arguments that satisfy the
precondition. The encoder drops the checks that the VCs prove, so the
comparison assumes them: where the Stainless program doesn't get stuck, both
must give the same result with the same fuel, an array being the same as the
map and size that the encoder makes of it. A mutation test checks that reading
Stainless's division as Inox's breaks the comparison.

This directory is the sbt project `stainless-proofs`. It is not published.

```sh
sbt stainless-proofs/test
sbt -Dsemantics-files=verification/valid/Heaps.scala stainless-proofs/test   # other benchmarks
```

After changing `semantics.md`, regenerate the evaluator and commit it with it;
a test fails while it is out of date:

```sh
sbt stainless-proofs/run
```
