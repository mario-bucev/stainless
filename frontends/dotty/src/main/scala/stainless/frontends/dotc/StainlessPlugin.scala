package stainless
package frontends.dotc

import dotty.tools.dotc.plugins.*
import inox.{Context, DebugSection, utils as InoxPosition}
import stainless.frontend
import stainless.frontend.{CallBack, Frontend}

class StainlessPlugin extends StandardPlugin {
  override val name: String = "Stainless"
  override val description: String = "Inject Stainless verification pipeline"

  def init(options: List[String]): List[PluginPhase] = {
    val mainHelper = new stainless.MainHelpers {
      override val factory = new frontend.FrontendFactory{
        override def apply(ctx: Context, compilerArgs: Seq[String], callback: CallBack): Frontend =
          sys.error("stainless.MainHelpers#factory should never be called from the dotty plugin")
        override protected val libraryPaths: Seq[String] = Seq.empty
      }
    }
    val stainlessContext: inox.Context =
      mainHelper.getConfigContext(inox.Options.empty)(using new stainless.PlainTextReporter(Set.empty))
    val cb = stainless.frontend.getCallBack(using stainlessContext)
    val cache: SymbolsContext = new SymbolsContext
    val phase = new StainlessExtraction(stainlessContext, cb, cache)
    List(phase)
  }
}
