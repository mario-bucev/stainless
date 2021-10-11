package stainless
package frontends.dotc
package plugin

import dotty.tools.dotc._
import core.Contexts.{Context => DottyContext}

import plugins._

import frontend.CallBack

class StainlessPhase(override val inoxCtx: inox.Context,
                     override val callback: CallBack,
                     override val cache: SymbolsContext,
                     override val dottyCtx: DottyContext)
  extends PluginPhase
     with StainlessExtraction
     with ASTExtractors {

  override val phaseName = "stainless"
  override val runsAfter = Set("typer")
  override val runsBefore = Set("patmat")

}
