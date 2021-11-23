package stainless
package frontends.dotc
package sbt

import utils.ExtractionCache
import extraction.xlang.trees as xt
import ast.SymbolIdentifier
import inox.{Context, OptionValue}
import stainless.frontend.{CallBack, Frontend}
import scala.util._
import java.io.File
import java.nio.file.Files

import scala.jdk.StreamConverters._

// TODO: Explain. Essentially called from SBT to verify extracted .bin stainless programs
class StainlessVerification {
  def verify(stainlessBinFolder: File): Unit = {
    val mainHelper = new stainless.MainHelpers {
      override val factory = new frontend.FrontendFactory{
        override def apply(ctx: Context, compilerArgs: Seq[String], callback: CallBack): Frontend =
          sys.error("stainless.MainHelpers#factory should never be called from the dotty plugin")
        override protected val libraryPaths: Seq[String] = Seq.empty
      }
    }
    given ctx: inox.Context = mainHelper.getConfigContext(inox.Options.empty)(using new stainless.DefaultReporter(Set.empty))

    val cb = stainless.frontend.getCallBack
    cb.beginExtractions()
/*
    val allDefsSyms: xt.Symbols = {
      val (cds, fds, tds) = ExtractionCache.readAllExtracted(stainlessBinFolder)
      val freshener = new SymbolFreshener
      val newCds = cds.map(freshener.transform)
      val newFds = fds.map(freshener.transform)
      val newTds = tds.map(freshener.transform)
      // Applying the same set of transformation as in Preprocessing
      val syms = xt.NoSymbols.withClasses(newCds).withFunctions(newFds).withTypeDefs(newTds)
      frontend.strictBVCleaner.transform(utils.LibraryFilter.removeLibraryFlag(syms))
    }
    println("There are " + allDefsSyms.functions.size + " functions")
    cb(
      // TODO
      "dummy",
      xt.UnitDef(FreshIdentifier("dummy"), Seq.empty, Seq.empty, Seq.empty, false),
      allDefsSyms.classes.values.toSeq,
      allDefsSyms.functions.values.toSeq,
      allDefsSyms.typeDefs.values.toSeq
    )
*/

    // TODO: Say something about this SymbolFreshener
    val freshener = new SymbolFreshener
    Files.walk(stainlessBinFolder.toPath).toScala(LazyList)
      .filter(p => Files.isRegularFile(p))
      .foreach { p =>
        ExtractionCache.readExtracted(p.toFile) match {
          case Success((unit, cds, fds, tds)) =>
            val (newUnit, syms) = freshener.withinUnit {
              val newUnit = freshener.transformUnit(unit)
              val newCds = cds.map(freshener.transform)
              val newFds = fds.map(freshener.transform)
              val newTds = tds.map(freshener.transform)
              // Applying the same set of transformation as in Preprocessing
              val syms = xt.NoSymbols.withClasses(newCds).withFunctions(newFds).withTypeDefs(newTds)
              (newUnit, frontend.strictBVCleaner.transform(utils.LibraryFilter.removeLibraryFlag(syms)))
            }
            cb(p.toFile.getName, newUnit, syms.classes.values.toSeq, syms.functions.values.toSeq, syms.typeDefs.values.toSeq)
          case Failure(e) =>
            ctx.reporter.error(e)
        }
      }


    cb.endExtractions()
    cb.join()

    cb.getReport.foreach(_.emit(ctx))
  }

  private class SymbolFreshener extends xt.ConcreteXLangSelfTreeTransformer {
    // Important: Note that we are not using SymbolIdentifier as keys, because their hash and equal method are
    // based on globalId, which are stale when reading them off the extracted files.
    // For instance, if we compile two files A.scala and B.scala separately (i.e. not in the same compilation run),
    // each of them containing the symbols def a and def b respectively, these methods may get the same global id.
    // If we read their extracted binary file later on, they would be considered "equal" due to their global id
    // being the same (even when they should not).
    // Instead, we are using their identifier name and symbol name.
    private val symIdMapping = scala.collection.mutable.Map.empty[(String, String), SymbolIdentifier]
    // Same story here.
    private val symMapping = scala.collection.mutable.Map.empty[String, ast.Symbol]

    private val idenMapping = scala.collection.mutable.Map.empty[(String, Int), Identifier]
    // TODO: Explain why. Also say can't be nested
    def withinUnit[T](op: => T): T = {
      idenMapping.clear()
      val res = op
      idenMapping.clear()
      res
    }

    override def transform(id: Identifier): Identifier = id match {
      case si: SymbolIdentifier =>
        symIdMapping.getOrElseUpdate((si.name, si.symbol.name), {
          val id = FreshIdentifier(si.name)
          val sym = symMapping.getOrElseUpdate(si.symbol.name, ast.Symbol(si.symbol.name))
          new SymbolIdentifier(id, sym)
        })
      case id => // TODO: Ensure that no plain Identifier can be referenced across compilation unit.
        idenMapping.getOrElseUpdate((id.name, id.globalId), FreshIdentifier(id.name))
    }

    override def transform(e: xt.Expr): xt.Expr = e match {
      // We need to explicitly transform LetClass to ensure we go through in each local methods
      // because the deconstructor of LetClass does not deconstruct local methods.
      case xt.LetClass(classes, body) =>
        xt.LetClass(classes.map(transform), transform(body))
      case e =>
        super.transform(e)
    }

    def transformUnit(unit: xt.UnitDef): xt.UnitDef =
      unit.copy(
        id = transform(unit.id),
        classes = unit.classes.map(transform),
        modules = unit.modules.map(transformModule))

    def transformModule(mod: xt.ModuleDef): xt.ModuleDef =
      mod.copy(
        id = transform(mod.id),
        classes = mod.classes.map(transform),
        functions = mod.functions.map(transform),
        typeDefs = mod.typeDefs.map(transform),
        modules = mod.modules.map(transformModule))
  }
}
