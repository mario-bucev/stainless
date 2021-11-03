/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package frontends.dotc

import dotty.tools.dotc._
import plugins._
import core.Contexts.{Context => DottyContext}
import core.Phases._
import transform._
import ast.Trees.PackageDef
import typer._

import extraction.xlang.{trees => xt}
import frontend.{CallBack, Frontend, FrontendFactory, ThreadedFrontend}

class StainlessExtraction(val inoxCtx: inox.Context,
                          val callback: CallBack,
                          val cache: SymbolsContext) extends PluginPhase {

  override val phaseName = "stainless"
  override val runsAfter = Set(Pickler.name) // TODO: Was typer then Pickeler
  override val runsBefore = Set(FirstTransform.name) // TODO: was PatternMatcher

  // TODO: we are overriding MiniPhase#run that is defined as singletonGroup.run. Is this ok?
  override def run(using ctx: DottyContext): Unit = {
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

    val fragmentChecker = new FragmentChecker(inoxCtx)
    fragmentChecker.ghostChecker(tree)
    fragmentChecker.checker(tree)

    if (!fragmentChecker.hasErrors()) {
      val (imports, unitClasses, unitFunctions, unitTypeDefs, subs, classes, functions, typeDefs, _) = extraction.extract(stats)
      assert(unitFunctions.isEmpty, "Packages shouldn't contain functions")

      val file = unit.source.file.absolute.path
      val isLibrary = stainless.Main.libraryFiles contains file
      val xtUnit = xt.UnitDef(id, imports, unitClasses, subs, !isLibrary)

      callback(file, xtUnit, classes, functions, typeDefs)
    }
  }
}
