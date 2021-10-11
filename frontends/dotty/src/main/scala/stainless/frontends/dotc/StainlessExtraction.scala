/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package frontends.dotc

import dotty.tools.dotc.*
import core.Contexts.*
import core.Phases.*
import transform.*
import ast.Trees.PackageDef
import typer.*

import extraction.xlang.{trees => xt}
import frontend.{CallBack, Frontend, FrontendFactory, ThreadedFrontend}

trait StainlessExtraction extends Phase {
  val inoxCtx: inox.Context
  val callback: CallBack
  val cache: SymbolsContext

  override def run(using ctx: Context): Unit = {
    val extraction = new CodeExtraction(inoxCtx, cache)
    import extraction._

    val unit = ctx.compilationUnit
    val tree = unit.tpdTree
    val (id, stats) = tree match {
      case pd @ PackageDef(refTree, lst) =>
        val id = lst.collectFirst { case PackageDef(ref, stats) => ref } match {
          case Some(ref) => extractRef(ref)
          case None => FreshIdentifier(unit.source.file.name.replaceFirst("[.][^.]+$", ""))
        }
        (id, pd.stats)
      case _ =>
        (FreshIdentifier(unit.source.file.name.replaceFirst("[.][^.]+$", "")), List.empty)
    }

    val (imports, unitClasses, unitFunctions, unitTypeDefs, subs, classes, functions, typeDefs) = extraction.extractStatic(stats)
    assert(unitFunctions.isEmpty, "Packages shouldn't contain functions")

    val file = unit.source.file.absolute.path
    // TODO
    val isLibrary = false // Main.libraryFiles contains file
    val xtUnit = xt.UnitDef(id, imports, unitClasses, subs, !isLibrary)

    callback(file, xtUnit, classes, functions, typeDefs)
  }
}
