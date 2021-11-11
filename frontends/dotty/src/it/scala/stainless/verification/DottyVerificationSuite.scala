/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification

import org.scalatest._

// TODO: Do something with this
trait DottyVerificationSuite extends VerificationComponentTestSuite {

  override def configurations = super.configurations.map {
    seq => optFailInvalid(true) +: seq
  }

  override protected def optionsString(options: inox.Options): String = {
    super.optionsString(options) +
    (if (options.findOptionOrDefault(evaluators.optCodeGen)) " codegen" else "")
  }

  override def filter(ctx: inox.Context, name: String): FilterStatus = name match {
    case _ => super.filter(ctx, name)
  }

//  def folder: String
//
//  testPosAll(folder)
}

/*
class SMTZ3DottyVerificationSuite extends DottyVerificationSuite {
  override def configurations = super.configurations.map {
    seq => Seq(
      inox.optSelectedSolvers(Set("smt-z3:z3-4.8.12")),
      inox.solvers.optCheckModels(true)
    ) ++ seq
  }

  def folder = "dotty-specific/valid"
}
*/