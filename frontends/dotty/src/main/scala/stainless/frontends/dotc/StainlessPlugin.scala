package stainless
package frontends.dotc
package plugin

import dotty.tools.dotc.plugins._

import inox.{Context, DebugSection, utils as InoxPosition}
import stainless.frontend.{CallBack, Frontend}

class StainlessPlugin extends StandardPlugin {
  override val name: String = "Stainless"
  override val description: String = "Inject Stainless verification pipeline"

  val mainHelper = new stainless.MainHelpers {
    override val factory = new frontend.FrontendFactory{
      override def apply(ctx: Context, compilerArgs: Seq[String], callback: CallBack): Frontend =
        sys.error("stainless.MainHelpers#factory should never be called from the dotty plugin")
      override protected val libraryPaths: Seq[String] = Seq.empty
    }
  }

  val stainlessContext: inox.Context = {
    given stainless.PlainTextReporter = new stainless.PlainTextReporter(Set.empty)
    mainHelper.getConfigContext(inox.Options.empty)
  }

  def init(options: List[String]): List[PluginPhase] = {
    ???
//    val setting = new Setting(options.headOption)
//    (new PhaseA(setting)) :: (new PhaseB(setting)) :: Nil
  }
}
