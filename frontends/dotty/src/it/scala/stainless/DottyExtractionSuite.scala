/* Copyright 2009-2021 EPFL, Lausanne */

package stainless

class DottyExtractionSuite extends ExtractionSuite {

  testExtractAll("extraction/valid")
  testRejectAll("extraction/invalid")

  testExtractAll("verification/valid")
  testExtractAll("verification/invalid")
  testExtractAll("verification/unchecked")

  testExtractAll("imperative/valid")
  testExtractAll("imperative/invalid")

  testExtractAll("termination/valid")
  testExtractAll("termination/looping")

//   TODO: Do something about these
//  testExtractAll("dotty-specific/valid")
//  testRejectAll("dotty-specific/invalid")

}