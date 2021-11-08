/* Copyright 2009-2021 EPFL, Lausanne */

package stainless

import stainless.extraction.xlang.{ trees => xt }
import stainless.extraction.utils.DebugSymbols

import org.scalatest.funspec.AnyFunSpec
import scala.util.{Success, Failure, Try}
import scala.collection.mutable

/** Subclass are only meant to call [[testExtractAll]] and [[testRejectAll]] on
 *  the relevant directories. */
abstract class ExtractionSuite extends AnyFunSpec with inox.ResourceUtils with InputUtils {

  def options: Seq[inox.OptionValue[_]] = Seq()

  final def createContext(options: inox.Options) = stainless.TestContext(options)

  private def testSetUp(dir: String): (inox.Context, List[String]) = {
    val ctx = createContext(inox.Options(options))
    val fs = resourceFiles(dir, _.endsWith(".scala")).toList map { _.getPath }
    (ctx, fs)
  }

  def testExtractAll(dir: String, excludes: String*): Unit = {
    val (ctx, allFiles) = testSetUp(dir)
    val files = allFiles.filter(f => !excludes.exists(f.endsWith))
    import ctx.{reporter, given}

    val userFiltering = new DebugSymbols {
      val name = "UserFiltering"
      val context = ctx
      val s: xt.type = xt
      val t: xt.type = xt
    }

    describe(s"Program extraction in $dir") {
      val tryProgram = scala.util.Try(loadFiles(files)._2)

      it("should be successful") { assert(tryProgram.isSuccess) }

      if (tryProgram.isSuccess) {
        val program = tryProgram.get
        val programSymbols: program.trees.Symbols =
          userFiltering.debug(frontend.UserFiltering().transform)(program.symbols)

        it("should typecheck") {
          programSymbols.ensureWellFormed
          for (fd <- programSymbols.functions.values.toSeq) {
            import programSymbols.{given, _}
            assert(isSubtypeOf(fd.fullBody.getType, fd.getType))
          }
        }

        val tryExSymbols: Try[extraction.trees.Symbols] = Try(extraction.pipeline extract programSymbols)
        describe("and transformation") {
          it("should be successful") { tryExSymbols.get }

          if (tryExSymbols.isSuccess) {
            val exSymbols = tryExSymbols.get
            it("should produce no errors") { assert(reporter.errorCount == 0) }

            it("should typecheck") {
              exSymbols.ensureWellFormed
              for (fd <- exSymbols.functions.values.toSeq) {
                import exSymbols.{given, _}
                assert(isSubtypeOf(fd.fullBody.getType, fd.getType))
              }
            }

            it("should typecheck without matches") {
              for (fd <- exSymbols.functions.values.toSeq) {
                import exSymbols.{given, _}
                assert(isSubtypeOf(matchToIfThenElse(fd.fullBody).getType, fd.getType))
              }
            }
          }
        }
      }
    }
  }

  // Tests that programs are rejected either through the extractor or through
  // the TreeSanitizer.
  def testRejectAll(dir: String, excludes: String*): Unit = {
    val (baseCtx, allfiles) = testSetUp(dir)
    val files = allfiles.filter(f => !excludes.exists(f.endsWith))

    val userFiltering = new DebugSymbols {
      val name = "UserFiltering"
      val context = baseCtx
      val s: xt.type = xt
      val t: xt.type = xt
    }

    describe(s"Programs extraction in $dir") {
      val tryPrograms = files.sorted.map { f =>
        val reporter = new NegativeTestReporter
        (f, reporter, Try {
          given testCtx: inox.Context = baseCtx.copy(reporter = reporter)
          val program = loadFiles(List(f))._2
          val programSymbols = userFiltering.debug(frontend.UserFiltering().transform)(program.symbols)
          extraction.pipeline extract programSymbols
          ()
        })
      }

      it("should fail") {
        tryPrograms.map {
          case (f, reporter, Success(())) =>
            (f, reporter.allErrors.mkString("\n"))
          case (f, reporter, Failure(e: extraction.MalformedStainlessCode)) =>
            reporter.error(e.tree.getPos, e.msg)
            (f, reporter.allErrors.mkString("\n"))
          case (f, reporter, Failure(inox.FatalError(_))) =>
            // The fatal error has been informed to the reporter, so we should not report it again.
            (f, reporter.allErrors.mkString("\n"))
          case (f, reporter, Failure(e)) =>
            throw new Exception(s"Unexpected exception for $f: \n$e")
        }.foreach {
          case (f, gotErrors) =>
            val checkFile = {
              Try(scala.io.Source.fromFile(f.replace(".scala", ".check")))
                .toOption
                .orElse {
                  val checkFile =
                    if (isScala2) f.replace(".scala", ".scalac.check")
                    else f.replace(".scala", ".dotty.check")
                  Try(scala.io.Source.fromFile(checkFile)).toOption
                }.getOrElse(fail(s"Could not find check file for negative test $f"))
            }
            val expected = checkFile.getLines().filterNot(_.trim.isEmpty).mkString("\n")
            if (gotErrors.isEmpty) {
              fail(s"No errors found for negative test $f")
            } else {
              assert(gotErrors == expected, s"Incorrect reported errors for negative test $f")
            }
        }
      }
    }
  }

  class NegativeTestReporter extends DefaultReporter(Set.empty) {
    val allErrors = mutable.ArrayBuffer.empty[String]

    override def emit(msg: Message): Unit = msg match {
      case Message(severity@(ERROR | FATAL), pos, msg) =>
        val errMsg = severityToPrefix(severity) + " " + msg + "\n" + lineContent(pos, asciiOnly = true)
        allErrors += errMsg
      case _ =>
    }

    override protected def severityToPrefix(sev: Severity): String = sev match {
      case ERROR => "[ Error  ]"
      case FATAL => "[ Fatal  ]"
      case _ => ""
    }
  }
}

