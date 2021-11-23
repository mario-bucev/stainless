package stainless
package frontends.dotc
package sbt

import dotty.tools.dotc
import dotc.*
import core.*
import util.*
import Contexts.Context as DottyContext
import plugins.*
import Phases.*
import transform.*
import reporting.*
import inox.{Context, DebugSection, utils as InoxPosition}
import stainless.frontend
import stainless.frontend.{CallBack, Frontend}
import stainless.utils.{Caches, ExtractionCache, Serializer}
import stainless.{ReportMessage, frontend}

import java.io.{DataOutputStream, File, FileOutputStream}
import java.nio.file.{Files, Paths}

object StainlessCompilerPlugin {
  val PluginName                              = "stainless"
  val PluginDescription                       = "Inject Stainless verification pipeline"
  val EnableGhostEliminationOptionName        = "ghost-elim:"
  val DisableIncrementalCompilationOptionName = "inc-comp:"
}

case class PluginOptions(enableGhostElimination: Boolean, enableIncComp: Boolean)

class StainlessCompilerPlugin extends StandardPlugin {
  import StainlessCompilerPlugin._

  override val name: String = PluginName
  override val description: String = PluginDescription

  def init(options: List[String]): List[PluginPhase] = {
    val pluginOpts = parseOptions(options)
    List(
      if (!pluginOpts.enableIncComp)
        Some(new ExtractionAndVerification)
      else
        Some(new ExtractionOnly),

      if (pluginOpts.enableGhostElimination)
        Some(new GhostAccessRewriter)
      else None
    ).flatten
  }

  private def parseOptions(options: List[String]): PluginOptions = {
    var enableGhostElimination = false
    var enableIncComp = true
    for (option <- options) {
      if (option.startsWith(EnableGhostEliminationOptionName)) {
        val value = option.substring(EnableGhostEliminationOptionName.length)
        parseBoolean(value) foreach { value =>
          enableGhostElimination = value
        }
      }
      else if (option.startsWith(DisableIncrementalCompilationOptionName)) {
        val value = option.substring(DisableIncrementalCompilationOptionName.length)
        parseBoolean(value) foreach { value =>
          enableIncComp = value
        }
      }
    }
    PluginOptions(enableGhostElimination = enableGhostElimination, enableIncComp = enableIncComp)
  }

  private def parseBoolean(str: String): Option[Boolean] =
    str match {
      case "false" | "no" => Some(false)
      case "true" | "yes" => Some(true)
      case _ => None
    }

  // Definitions that are common to both ExtractionOnly and ExtractionAndVerification phases
  private object Common {
    val phaseName = "stainless"
    val runsAfter = Set(Pickler.name)
    val runsBefore = Set(FirstTransform.name)

    def createContext(using DottyContext): inox.Context = {
      val mainHelper = new stainless.MainHelpers {
        override val factory = new frontend.FrontendFactory{
          override def apply(ctx: Context, compilerArgs: Seq[String], callback: CallBack): Frontend =
            sys.error("stainless.MainHelpers#factory should never be called from the dotty plugin")
          override protected val libraryPaths: Seq[String] = Seq.empty
        }
      }

      val base = mainHelper.getConfigContext(inox.Options.empty)(using new stainless.PlainTextReporter(Set.empty))
      val adapter = new ReporterAdapter(base.reporter.debugSections)
      val batched = inox.OptionValue(frontend.optBatchedProgram)(true)
      inox.Context(
        reporter         = adapter,
        interruptManager = new inox.utils.InterruptManager(adapter),
        options          = base.options + batched,
        timers           = base.timers,
      )
    }
  }

  private class ExtractionOnly extends PluginPhase {
    override val phaseName = Common.phaseName
    override val runsAfter = Common.runsAfter
    override val runsBefore = Common.runsBefore

    private var inoxCtx: Option[inox.Context] = None
    private var fileMapping: Option[Map[CompilationUnit, File]] = None
    private var extraction: Option[StainlessExtraction] = None

    override def run(using DottyContext): Unit =
      extraction.get.extractUnit.foreach(writeExtracted)

    override def runOn(units: List[CompilationUnit])(using DottyContext): List[CompilationUnit] = {
      val inoxCtx0 = Common.createContext
      val fileMapping0 = createFileMapping(units)
      // Not pretty at all... Oh well...
      inoxCtx = Some(inoxCtx0)
      fileMapping = Some(fileMapping0)
      // The instance StainlessExtraction must be preserved across all compilation units, that's why we have
      // it as a field and not a local val in `run`.
      // See StainlessExtraction for more information.
      extraction = Some(new StainlessExtraction(inoxCtx0))
      super.runOn(units)
    }

    private def createFileMapping(units: List[CompilationUnit])(using dottyCtx: DottyContext): Map[CompilationUnit, File] = {
      import scala.jdk.CollectionConverters.*
      val extractedOutDir = {
        val scalaOut = new File(dottyCtx.settings.outputDir.value.absolutePath)
        if (scalaOut.getName == "classes") new File(scalaOut.getParentFile, "stainless")
        else scalaOut
      }
      val outDirParts = extractedOutDir.toPath.iterator.asScala.map(_.toFile.getName).toSeq
      // For each compilation unit, we are going to create a .bin file containing the extracted trees.
      units.map { unit =>
        val srcParts = Paths.get(unit.source.file.absolute.path)
          .iterator.asScala.map(_.toFile.getName).toSeq
        val commonAncestors = outDirParts.zip(srcParts).takeWhile((o, s) => o == s)
        val outExtractedFilename = {
          val relative0 = srcParts.drop(commonAncestors.size)
          if (relative0.startsWith(List("src", "main", "scala"))) relative0.drop(3)
          else relative0
        }.mkString("/").replace(".scala", ".bin")
        unit -> new File(extractedOutDir, outExtractedFilename)
      }.toMap
    }

    private def writeExtracted(extracted: ExtractedUnit)(using dottyCtx: DottyContext): Unit = {
      val fileMapping0 = fileMapping.get
      ExtractionCache.writeExtracted(fileMapping0(dottyCtx.compilationUnit), extracted.unit, extracted.classes, extracted.functions, extracted.typeDefs)
    }
  }

  private class ExtractionAndVerification extends PluginPhase {
    override val phaseName = Common.phaseName
    override val runsAfter = Common.runsAfter
    override val runsBefore = Common.runsBefore

    private var extraction: Option[StainlessExtraction] = None
    private var callback: Option[CallBack] = None

    // This method id called for every compilation unit, and in the same thread.
    // It is called within super.runOn.
    override def run(using DottyContext): Unit =
      extraction.get.extractUnit.foreach { extracted =>
        callback.get(extracted.file, extracted.unit, extracted.classes, extracted.functions, extracted.typeDefs)
      }

    override def runOn(units: List[CompilationUnit])(using dottyCtx: DottyContext): List[CompilationUnit] = {
      val inoxCtx = Common.createContext
      val cb = stainless.frontend.getCallBack(using inoxCtx)
      // Not pretty at all... Oh well...
      callback = Some(cb)
      // The instance StainlessExtraction must be preserved across all compilation units, that's why we have
      // it as a field and not a local val in `run`.
      // See StainlessExtraction for more information.
      extraction = Some(new StainlessExtraction(inoxCtx))

      cb.beginExtractions()
      val unitRes = super.runOn(units)
      cb.endExtractions()
      cb.join()

      cb.getReport.foreach(_.emit(inoxCtx))
      unitRes
    }
  }

  class ReporterAdapter(debugSections: Set[DebugSection])(using dottyCtx: DottyContext) extends inox.PlainTextReporter(debugSections) {
    import dotty.tools.io._
    import Diagnostic._
    import Message._

    private def toSourceFile(file: java.io.File): SourceFile =
      SourceFile(AbstractFile.getFile(file.getPath), scala.io.Codec.UTF8)

    private def toDottyPos(pos: InoxPosition.Position): SourcePosition = pos match {
      case InoxPosition.NoPosition =>
        NoSourcePosition

      case InoxPosition.OffsetPosition(_, _, point, file) =>
        SourcePosition(toSourceFile(file), Spans.Span(point, point, point))

      case InoxPosition.RangePosition(_, _, pointFrom, _, _, pointTo, file) =>
        SourcePosition(toSourceFile(file), Spans.Span(pointFrom, pointFrom, pointTo))
    }

    override def emit(message: Message): Unit = {
      val pos = toDottyPos(message.position)

      message.msg match {
        case msg: ReportMessage =>
          msg.emit(this)

        case msg: String =>
          message.severity match {
            case INFO                     => dottyCtx.reporter.report(Info(msg, pos))
            case WARNING                  => dottyCtx.reporter.report(Warning(msg, pos))
            case ERROR | FATAL | INTERNAL => dottyCtx.reporter.report(Diagnostic.Error(msg, pos))
            case _                        => dottyCtx.reporter.report(Info(msg, pos)) // DEBUG messages are at reported at INFO level
          }

        case _ => ()
      }
    }
  }
}
