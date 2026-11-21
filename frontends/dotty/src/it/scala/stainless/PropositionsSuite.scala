/* Copyright 2009-2026 EPFL, Lausanne */

package stainless

/** Checks that quantifiers are propositions: they can be stated in specifications, lemmas and
  * predicate definitions, but the value of a term can't depend on them. */
class PropositionsSuite extends ExtractionSuite {
  testExtractAll("propositions/valid")
  testRejectAll("propositions/invalid")
}
