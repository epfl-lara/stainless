/* Copyright 2009-2021 EPFL, Lausanne */

package stainless

class ScalacExtractionSuite extends ExtractionSuite {

  testExtractAll("extraction/valid")
  testRejectAll("extraction/invalid",
    // This file is extracted because there is no -Ysafe-init check equivalent in Scala 2 (and not caught by Stainless either)
    "Initialization6.scala")

  testExtractAll("verification/valid")
  testExtractAll("verification/invalid")
  testExtractAll("verification/unchecked")

  testExtractAll("imperative/valid")
  testExtractAll("imperative/invalid")

  testExtractAll("termination/valid")
  testExtractAll("termination/looping")

}

