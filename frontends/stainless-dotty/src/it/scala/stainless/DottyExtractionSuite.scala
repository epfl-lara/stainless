/* Copyright 2009-2018 EPFL, Lausanne */

package stainless

class DottyExtractionSuite extends ExtractionSuite {

  testExtractAll("verification/valid")
  testExtractAll("verification/invalid")
  testExtractAll("verification/unchecked")
  testExtractAll("imperative/valid")
  testExtractAll("imperative/invalid")
  testExtractAll("termination/valid")
  testExtractAll("termination/looping")
  testExtractAll("extraction/valid")
  testRejectAll("extraction/invalid",
    "extraction/invalid/TypeMember.scala",
    "extraction/invalid/Println.scala",
    "extraction/invalid/CtorParams.scala",
    "extraction/invalid/ClassBody.scala",
    "extraction/invalid/Require.scala",
    "extraction/invalid/ghost-patmat.scala",
    "extraction/invalid/ghost-dafny.scala"
  )

}

