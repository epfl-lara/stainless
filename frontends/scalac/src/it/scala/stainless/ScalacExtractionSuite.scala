/* Copyright 2009-2018 EPFL, Lausanne */

package stainless

class ScalacExtractionSuite extends ExtractionSuite {

  testExtractAll("extraction/valid",
    "extraction/valid/AccessorFlags.scala", // FIXME
  )
  testRejectAll("extraction/invalid",
    "extraction/invalid/TraitVar1.scala", // FIXME
  )

  testExtractAll("verification/valid")
  testExtractAll("verification/invalid")
  testExtractAll("verification/unchecked")

  testExtractAll("imperative/valid",
    "imperative/valid/Blocks1.scala",
    "imperative/valid/TraitVar1.scala", // FIXME
    "imperative/valid/TraitVar2.scala", // FIXME
  )
  testExtractAll("imperative/invalid")

  testExtractAll("termination/valid")
  testExtractAll("termination/looping")

}

