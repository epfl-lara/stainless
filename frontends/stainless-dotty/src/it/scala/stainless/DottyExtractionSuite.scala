/* Copyright 2009-2018 EPFL, Lausanne */

package stainless

class DottyExtractionSuite extends ExtractionSuite {

  testExtractAll("verification/valid")
  testExtractAll("verification/invalid")
  testExtractAll("verification/unchecked")
  testExtractAll("imperative/valid",
    "imperative/valid/Snapshot2.scala" // excluded due to https://github.com/epfl-lara/stainless/issues/419
  )
  testExtractAll("imperative/invalid")
  testExtractAll("termination/valid")
  testExtractAll("termination/looping")
  testExtractAll("extraction/valid",
    "extraction/valid/AccessorFlags.scala",
    "extraction/valid/ghost-caseclass.scala",
    "extraction/valid/GhostEffect3.scala",
    "extraction/valid/GhostFlow1.scala",
    "extraction/valid/GhostFlow2.scala",
    "extraction/valid/GhostFlow3.scala")
  testRejectAll("extraction/invalid",
    "extraction/invalid/TypeMember.scala",
    "extraction/invalid/Println.scala",
    "extraction/invalid/CtorParams.scala",
    "extraction/invalid/ClassBody.scala",
    "extraction/invalid/Require.scala",
    "extraction/invalid/GhostEffect3.scala",
    "extraction/invalid/ghost-patmat.scala",
    "extraction/invalid/ghost-dafny.scala",
    "extraction/invalid/SuperAbstract.scala")

}

