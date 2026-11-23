# Semantics of Stainless's trees

[`semantics.md`](semantics.md) defines what Stainless's expressions mean, as an
extension of [Inox's semantics](../inox/proofs/semantics.md): it imports Inox's
file and adds the expressions that Stainless has and Inox doesn't. A run that
violates a contract gets stuck, as one where an `assume` doesn't hold does.
Verification rules out the first, and the second is the trusted base. Inox's
expressions keep their meaning. The goal is a semantics per tree layer, each extending the one below
as the trees do, so that each extraction phase can be stated, tested and then
proved in Lean to preserve meaning.

This version covers the last layer, `stainless.ast`, in a fragment: contracts,
pattern matching on constructors, tuples and literals, and the JVM's integer
division.

`EncoderSemanticsSuite` tests `InoxEncoder`, the last step into Inox. On the
functions of some verification benchmarks, and of a sample with negative
divisions and violated contracts, it compares the program that the extraction
produces, under Stainless's semantics, with the program that `InoxEncoder`
makes of it, under Inox's, on random arguments that satisfy the precondition.
The encoder drops the checks that the VCs prove, so the comparison assumes
them: where the Stainless program doesn't get stuck, both must give the same result
with the same fuel. A mutation test checks that reading Stainless's division
as Inox's breaks the comparison.

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
