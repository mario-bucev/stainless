package stainless
package verification

import scala.util.Try

trait VerificationComponentTestSuite extends ComponentTestSuite { self =>

  override val component: VerificationComponent.type = VerificationComponent

  override def configurations = super.configurations.map { seq =>
    Seq(
      // We do not fail on early/invalid VCs for negative test cases
      optFailInvalid(false),
      optFailEarly(false)
    ) ++ seq
  }

  def testPosAll(dir: String, recursive: Boolean = false, keepOnly: String => Boolean = _ => true, identifierFilter: Identifier => Boolean = _ => true): Unit =
    testAll(dir, recursive, keepOnly, identifierFilter) { (analysis, reporter, _) =>
      assert(analysis.toReport.stats.validFromCache == 0, "no cache should be used for these tests")
      for ((vc, vr) <- analysis.vrs) {
        if (vr.isInvalid) fail(s"The following verification condition was invalid: $vc @${vc.getPos}")
        if (vr.isInconclusive) fail(s"The following verification condition was inconclusive: $vc @${vc.getPos}")
      }
      reporter.terminateIfError()
    }

  // TODO: Comment
  // Note: testNegAll does not allow recursive directory to avoid the case where two units have the same name
  // but are not in the same folder, as we cannot determine which checkfile we need to pick.
  def testNegAll(dir: String, keepOnly: String => Boolean = _ => true, identifierFilter: Identifier => Boolean = _ => true): Unit = {
    val allCheckFiles = resourceFiles(dir,
      f => f.contains(".check") && (!f.contains(".scalac.check") || isScala2) && (!f.contains(".dotty.check") || isScala3),
      recursive = false)

    testAll(dir, recursive = false, keepOnly, identifierFilter) { (analysis, reporter, unit) =>
      val report = analysis.toReport
      // First, ensure there is at least one invalid VC
      assert(report.totalInvalid > 0, "There should be at least one invalid verification condition. " + report.stats)
      val got = report.results
        .filterNot(_.status.isValid)
        .sortBy(record => (record.pos.line, record.pos.col, record.id.name, record.status.name, record.kind))
        .map(record => s"${record.pos} ${record.id} ${record.status.name} ${record.kind}")
        .mkString("\n")

      val checkFiles = allCheckFiles.filter(_.getName.replace(".scalac", "").replace(".dotty", "").startsWith(s"${unit.id.name}.check"))
      if (checkFiles.isEmpty) {
//        fail(s"No check file found for ${unit.id.name}")
      }
      val checkFilesContent = checkFiles.view.map(f => scala.io.Source.fromFile(f).getLines().filterNot(_.trim.isEmpty).mkString("\n"))
      if (!checkFilesContent.contains(got)) {
        println("-----------------------------------")
        println(s"Got the following for ${unit.id.name}:")
        println(got)
        println("-----------------------------------")
      }
      // assert(checkFilesContent.contains(got))
    }
  }
}