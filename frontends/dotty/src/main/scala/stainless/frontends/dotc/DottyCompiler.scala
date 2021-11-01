/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package frontends.dotc

import dotty.tools.dotc.*
import dotty.tools.dotc.reporting.{Diagnostic, Reporter as DottyReporter}
import dotty.tools.dotc.interfaces.Diagnostic.{ERROR, WARNING, INFO}
import plugins.Plugins
import dotty.tools.dotc.util.SourcePosition
import dotty.tools.io.AbstractFile
import core.Contexts.{Context as DottyContext, *}
import core.Phases.*
import transform.*
import typer.*
import frontend.{CallBack, Frontend, FrontendFactory, ThreadedFrontend}

class DottyCompiler(ctx: inox.Context, callback: CallBack, cache: SymbolsContext) extends Compiler {
  override def phases: List[List[Phase]] = {
    val allOrigPhases = super.phases
    val stainless = new StainlessExtraction(ctx, callback, cache)
    val ph = Plugins.schedule(allOrigPhases, List(stainless))
    ph
  }
}

private class DottyDriver(args: Seq[String], compiler: DottyCompiler, reporter: DottyReporter) extends Driver {
  override def newCompiler(using DottyContext) = compiler

  lazy val files: List[String] = setup(args.toArray, initCtx).map(_._1.map(_.path)).getOrElse(Nil)

  def run(): Unit = process(args.toArray, reporter)
}

private class SimpleReporter(val reporter: inox.Reporter) extends DottyReporter {
  final val ERROR_LIMIT = 5

  val count = scala.collection.mutable.Map[Int, Int](
    ERROR   -> 0,
    WARNING -> 0,
    INFO    -> 0,
  )

  def printMessage(msg: String, pos: inox.utils.Position, severity: Int): Unit = severity match {
    case `ERROR` =>
      reporter.error(pos, msg)
    case `WARNING` =>
      reporter.warning(pos, msg)
    case `INFO` =>
      reporter.info(pos, msg)
    case _ =>
      throw new Exception("Severity should be one of ERROR, WARNING, INFO")
  }

  /** Prints the message with the given position indication. */
  def printMessage(pos: SourcePosition, msg: String, severity: Int): Unit = {
    if (!pos.exists) {
      printMessage(msg, inox.utils.NoPosition, severity)
    } else {
      val lpos = inox.utils.OffsetPosition(pos.line, pos.column, pos.point, pos.source.file.file)
      printMessage(msg, lpos, severity)
    }
  }

  def doReport(dia: Diagnostic)(using DottyContext): Unit = printMessage(dia.pos, dia.msg.message, dia.level)
}

object DottyCompiler {

  /** Complying with [[frontend]]'s interface */
  class Factory(
    override val extraCompilerArguments: Seq[String],
    override val libraryPaths: Seq[String]
  ) extends FrontendFactory {

    override def apply(ctx: inox.Context, compilerArgs: Seq[String], callback: CallBack): Frontend =
      new ThreadedFrontend(callback, ctx) {
        val cache = new SymbolsContext
        val args = {
          // TODO: Explain this mess
          // Attempt to find where the scala libs are.
          val scala213Lib: String = Option(scala.Predef.getClass.getProtectionDomain.getCodeSource) map {
            _.getLocation.getPath
          } getOrElse { ctx.reporter.fatalError("No Scala 2.13 library found.") }
          val scala3Lib: String = Option(scala.util.NotGiven.getClass.getProtectionDomain.getCodeSource) map {
            _.getLocation.getPath
          } getOrElse { ctx.reporter.fatalError("No Scala 3 library found.") }
          val flags = Seq("-color:never", "-language:implicitConversions", s"-cp:$scala213Lib:$scala3Lib")
          val res = allCompilerArguments(ctx, compilerArgs) ++ flags
          res
        }
        val compiler: DottyCompiler = new DottyCompiler(ctx, this.callback, cache)

        val driver = new DottyDriver(args, compiler, new SimpleReporter(ctx.reporter))

        override val sources = driver.files

        override def initRun(): Unit = ()

        override def onRun(): Unit = driver.run()

        override def onEnd(): Unit = ()

        override def onStop(thread: Thread): Unit = {
          // TODO implement a graceful stop! Current implementation might not work anyway...
          thread.join()
        }
      }
  }
}