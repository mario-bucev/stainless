/* Copyright 2009-2021 EPFL, Lausanne */

package stainless

class DottyExtractionSuite extends ExtractionSuite {

//  testExtractAll("extraction/valid")
  // TODO: Be sure they are rejected for good reasons
   testRejectAll("extraction/invalid")

//  testExtractAll("verification/valid")
//  testExtractAll("verification/invalid")
//  testExtractAll("verification/unchecked")
//
//  testExtractAll("imperative/valid")
//  testExtractAll("imperative/invalid")
//
//  testExtractAll("termination/valid")
//  testExtractAll("termination/looping")


  // TODO: Be sure they are rejected for good reasons
  /*
  testRejectAll("extraction/invalid",
    "extraction/invalid/TypeMember.scala",
    "extraction/invalid/Println.scala",
    "extraction/invalid/CtorParams.scala",
    "extraction/invalid/ClassBody.scala",
    "extraction/invalid/Require.scala",
    "extraction/invalid/GhostEffect3.scala",
    "extraction/invalid/GhostPatmat.scala",
    "extraction/invalid/GhostDafny.scala",
    "extraction/invalid/SuperAbstract.scala",
    "extraction/invalid/SuperAbstract.scala",
    "extraction/invalid/AnonymousClassRefine.scala",
  )*/

//  testExtractAll("dotty-specific/valid")
//  testRejectAll("dotty-specific/invalid")

}

