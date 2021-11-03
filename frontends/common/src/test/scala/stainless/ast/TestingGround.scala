/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package ast

import inox.Options
import org.scalatest.funsuite.AnyFunSuite
import stainless.verification.optTypeChecker

class TestingGround extends AnyFunSuite with InputUtils {

  val tayst = List(
    """import stainless.lang._
      |import stainless.proof._
      |import stainless.math._
      |import BitVectors._
      |
      |object Tayst {
      |  def limsup: Int = ???
      |}
      |
      |case class SomeClass() {
      |  def helloFriend: Int = {
      |    Tayst.limsup
      |  }
      |  def helloOld5Friend(x: Array[String], i: Int10): Unit = {
      |    val w = x(i)
      |    ()
      |  }
      |  def helloOld4Friend(x: Int): Unit = {
      |    val y = Array.fill(x)(x + 1)
      |    val z = Array(1, 2, 3, 4)
      |    y(1) = 42
      |    val w = y.size
      |    val ww = y.length
      |    val www = y(3)
      |    ()
      |  }
      |
      |  def helloOld3Friend(x: Int): Unit = {
      |    val y = Array.empty[Int]
      |    val z = Array.empty[String]
      |    ()
      |  }
      |
      |  def helloOld2Friend(x: Int): Boolean = {
      |    val y = "13241".bigLength()
      |    true
      |  }.holds because { x + x == 4 }
      |
      |  def helloOldFriend(x: Int): Boolean = {
      |    x == 2
      |  }.holds because { x + x == 4 }
      |}""".stripMargin)

  val tayst2 = List(
    """
      |object GhostDafny {
      |  import stainless.annotation._
      |
      |  sealed abstract class GhostDt
      |  case class Nilly(@ghost extraInfo: BigInt) extends GhostDt
      |
      |  object GhostTests {
      |    def M(dt: GhostDt): Unit = {
      |      @ghost var g: BigInt = 5
      |      var dd: GhostDt = Nilly(0);
      |      dd = Nilly(g);  // fine
      |    }
      |  }
      |}""".stripMargin)

  val ctx: inox.Context = stainless.TestContext.empty
//  val ctx: inox.Context = stainless.TestContext(Options(Seq(optTypeChecker(true))))
  import ctx.given
  // verification/valid/FunctionMapsObj.scala
  // verification/valid/StateMachine.scala
  // verification/valid/FunctionMaps.scala
  // verification/valid/Iterables.scala
  // verification/valid/ValueClassesInv.scala
  // verification/invalid/ADTInitialization.scala
  // verification/valid/MicroTests/Monads1.scala
  lazy val fromFile = List(scala.io.Source.fromFile("frontends/benchmarks/full-imperative/valid/AsHeapRefSet").mkString)
  val (_, xlangProgram) = load(tayst2)
  val x = 3
//  val run = verification.VerificationComponent.run(extraction.pipeline)
//  val program = inox.Program(run.trees)(run extract xlangProgram.symbols)

  import stainless.trees.*
  test("dummy") {
    true
  }
}
