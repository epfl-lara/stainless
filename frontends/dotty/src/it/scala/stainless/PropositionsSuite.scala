/* Copyright 2009-2026 EPFL, Lausanne */

package stainless

import inox.ast.{optQuantifiers, QuantifierMode}

/** Checks which programs type under `--quantifiers=propositional`, where quantifiers are
  * propositions that the value of a term can't depend on. */
class PropositionsSuite extends ExtractionSuite {
  override def options = Seq(optQuantifiers(QuantifierMode.Propositional))

  testExtractAll("propositions/valid")
  testRejectAll("propositions/invalid")

  // The benchmarks that only state specifications with their quantifiers. The excluded ones
  // return predicates as lambdas, or decide between two proofs with a quantifier.
  testExtractAll("verification/valid", "Predicate.scala", "ForallExistsTest.scala")
}
