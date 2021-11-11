/* Copyright 2009-2021 EPFL, Lausanne */

package stainless

class DottyExtractionSuite extends ExtractionSuite {

  testExtractAll("extraction/valid")
  testRejectAll("extraction/invalid",
    // These tests are actually extracted, due to our needs of handling given instances (see ASTExtractor.ExFancyObjectDef).
    "ObjectParent1.scala",
    "ObjectParent2.scala")

  testExtractAll("verification/valid")
  testExtractAll("verification/invalid")
  testExtractAll("verification/unchecked")

  testExtractAll("imperative/valid")
  testExtractAll("imperative/invalid")

  testExtractAll("termination/valid")
  testExtractAll("termination/looping")

  testExtractAll("dotty-specific/valid",
    "ConstructorRefinement.scala",
    "IdentityRefinement.scala",
    "PositiveInt.scala",
    "PositiveIntAlias.scala",
    "RefinedTypeMember.scala",
    "SortedListHead.scala",
    "ErasedTerms1.scala")

  testRejectAll("dotty-specific/extraction-reject")
}