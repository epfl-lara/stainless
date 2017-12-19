/* Copyright 2009-2017 EPFL, Lausanne */

package stainless

class ScalacExtractionSuite extends ExtractionSuite {

  testExtractAll("extraction/valid")
  testRejectAll("extraction/invalid")

}

